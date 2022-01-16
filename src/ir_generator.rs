use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::passes::PassManager;
use inkwell::types::BasicMetadataTypeEnum;
use inkwell::values::{BasicValue, FloatValue, FunctionValue, PointerValue};
use inkwell::FloatPredicate;
use std::collections::HashMap;

use crate::parser::AstNode;
use crate::parser::Expression;
use crate::parser::Function;
use crate::parser::Prototype;

enum IrRetVal<'ctx> {
    Expr(FloatValue<'ctx>),
    Func(FunctionValue<'ctx>),
}

type ExprIrResult<'ctx> = Result<FloatValue<'ctx>, String>;
type FuncIrResult<'ctx> = Result<FunctionValue<'ctx>, String>;

pub struct IrGenerator<'a, 'ctx> {
    context: &'ctx Context,
    builder: &'a Builder<'ctx>,
    module: &'a Module<'ctx>,
    fpm: &'a PassManager<FunctionValue<'ctx>>,
    values: HashMap<String, PointerValue<'ctx>>,
}

impl<'a, 'ctx> IrGenerator<'a, 'ctx> {
    pub fn new(
        context: &'ctx Context,
        builder: &'a Builder<'ctx>,
        module: &'a Module<'ctx>,
        fpm: &'a PassManager<FunctionValue<'ctx>>,
    ) -> Self {
        let values = HashMap::new();

        fpm.add_instruction_combining_pass();
        fpm.add_reassociate_pass();
        fpm.add_gvn_pass();
        fpm.add_cfg_simplification_pass();
        fpm.initialize();

        IrGenerator {
            context,
            builder,
            module,
            fpm,
            values,
        }
    }

    // taken from inkwell example
    // todo: figure out what this is
    fn create_entry_block_alloca(&self, name: &str, func: &FunctionValue) -> PointerValue<'ctx> {
        let builder = self.context.create_builder();

        let entry = func.get_first_basic_block().unwrap();

        match entry.get_first_instruction() {
            Some(first_instr) => builder.position_before(&first_instr),
            None => builder.position_at_end(entry),
        }

        builder.build_alloca(self.context.f64_type(), name)
    }

    // Iterate over all nodes and generate IR. Optionally return a string (for
    // testing).
    pub fn generate(&mut self, ast: &[AstNode]) -> Result<FunctionValue, String> {
        let mut main: Option<FunctionValue> = None;
        for node in ast {
            let ir = match node {
                AstNode::Expr(expr) => IrRetVal::Expr(self.gen_expr_ir(expr)?),
                AstNode::Proto(proto) => IrRetVal::Func(self.gen_proto_ir(proto)?),
                AstNode::Func(func) => IrRetVal::Func(self.gen_func_ir(func)?),
            };

            if let IrRetVal::Func(f) = ir {
                if f.get_name().to_str().unwrap() == "main" {
                    main = Some(f);
                }
            }
        }

        // Return main
        if let Some(m) = main {
            Ok(m)
        } else {
            Err(String::from("main() not found"))
        }
    }

    fn gen_proto_ir(&self, proto: &Prototype) -> FuncIrResult<'ctx> {
        let f64_type = self.context.f64_type();
        let args_type = proto
            .args
            .iter()
            .map(|_| f64_type.into())
            .collect::<Vec<BasicMetadataTypeEnum>>();

        let func_type = f64_type.fn_type(&args_type, false);
        let func = self.module.add_function(&proto.name, func_type, None);

        func.get_param_iter().enumerate().for_each(|(i, arg)| {
            arg.into_float_value().set_name(&proto.args[i]);
        });

        Ok(func)
    }

    fn gen_func_ir(&mut self, func: &Function) -> FuncIrResult<'ctx> {
        let function = self.gen_proto_ir(&func.proto)?;
        let body = match func.body.as_ref() {
            Some(body) => body,
            None => return Ok(function), // is extern
        };

        let bb = self.context.append_basic_block(function, "entry");
        self.builder.position_at_end(bb);

        self.values.reserve(func.proto.args.len());
        for (i, arg) in function.get_param_iter().enumerate() {
            let arg_name = &func.proto.args[i];
            let alloca = self.create_entry_block_alloca(arg_name, &function);
            self.builder.build_store(alloca, arg);
            self.values.insert(arg_name.to_owned(), alloca);
        }

        let mut last_expr: Option<Box<dyn BasicValue>> = None;
        for e in body {
            last_expr = Some(Box::new(self.gen_expr_ir(e)?));
        }
        self.builder.build_return(last_expr.as_deref());

        if function.verify(true) {
            self.fpm.run_on(&function);
            Ok(function)
        } else {
            unsafe {
                // TODO: Do we care about this for AOT comiplation?
                function.delete();
            }
            Err(String::from("Bad function generation"))
        }
    }

    fn gen_expr_ir(&self, expr: &Expression) -> ExprIrResult<'ctx> {
        match expr {
            Expression::Num { value: v } => self.gen_num_ir(*v),
            Expression::Var { name: n } => self.gen_var_ir(n),
            Expression::BinOp { op, lhs, rhs } => self.gen_binop_ir(*op, lhs, rhs),
            Expression::Call { name, args } => self.gen_call_ir(name, args),
            Expression::Cond { cond, cons, alt } => self.gen_cond_ir(cond, cons, alt),
        }
    }

    fn gen_num_ir(&self, num: f64) -> ExprIrResult<'ctx> {
        Ok(self.context.f64_type().const_float(num))
    }

    fn gen_var_ir(&self, name: &str) -> ExprIrResult<'ctx> {
        match self.values.get(name) {
            Some(var) => Ok(self.builder.build_load(*var, name).into_float_value()),
            None => Err(format!("Unknown variable: {}", name)),
        }
    }

    fn gen_binop_ir(&self, op: char, lhs: &Expression, rhs: &Expression) -> ExprIrResult<'ctx> {
        let lhs = self.gen_expr_ir(lhs)?;
        let rhs = self.gen_expr_ir(rhs)?;

        match op {
            '*' => Ok(self.builder.build_float_mul(lhs, rhs, "tmpmul")),
            '/' => Ok(self.builder.build_float_div(lhs, rhs, "tmpdiv")),
            '+' => Ok(self.builder.build_float_add(lhs, rhs, "tmpadd")),
            '-' => Ok(self.builder.build_float_sub(lhs, rhs, "tmpsub")),
            op @ ('>' | '<') => {
                let res = if op == '>' {
                    self.builder
                        .build_float_compare(FloatPredicate::UGT, lhs, rhs, "tmpcmp")
                } else {
                    self.builder
                        .build_float_compare(FloatPredicate::ULT, lhs, rhs, "tmpcmp")
                };
                Ok(self.builder.build_unsigned_int_to_float(
                    res,
                    self.context.f64_type(),
                    "tmpbool",
                ))
            }
            x => Err(format!("Unknown binary operator: {}", x)),
        }
    }

    fn gen_call_ir(&self, name: &str, args: &[Expression]) -> ExprIrResult<'ctx> {
        let func = self
            .module
            .get_function(name)
            .ok_or(format!("Unknown function call: {}", name))?;

        let mut args_ir = Vec::with_capacity(args.len());
        for arg in args {
            args_ir.push(self.gen_expr_ir(arg)?.into());
        }

        match self
            .builder
            .build_call(func, &args_ir, "tmpcall")
            .try_as_basic_value()
            .left()
        {
            Some(v) => Ok(v.into_float_value()),
            None => Err(String::from("Invalid call?")),
        }
    }

    /* Generates IR for conditionals. IR roughly looks like:
     *              |condition|
     *                 |   |
     *       ----------     ----------
     *      |                         |
     *      v                         v
     * |consequent|              |alternative|
     *      |                         |
     *       ----------     ----------
     *                 |   |
     *                 v   v
     *              |merge (phi)|
     */
    fn gen_cond_ir(
        &self,
        cond: &Expression,
        cons: &Expression,
        alt: &Option<Box<Expression>>,
    ) -> ExprIrResult<'ctx> {
        // Get the current function for insertion
        let parent = self
            .builder
            .get_insert_block()
            .and_then(|x| x.get_parent())
            .ok_or("Parent function not found when building conditional")?;

        let zero_const = self.context.f64_type().const_float(0.0);

        // Gen cond expression IR. Will be optimized to a 0 or 1 if comparing
        // constants. Otherwise, the value will be IR to evaluate. Result will
        // be a float 0.0 or 1.0.
        let cond_ir = self.gen_expr_ir(cond)?;

        // Gen IR to compare the cond_ir (0 or 1) to 0. Result will be a 1 bit
        // "bool".
        let cond_bool =
            self.builder
                .build_float_compare(FloatPredicate::ONE, cond_ir, zero_const, "ifcond");

        // Create blocks for branches and after (phi)
        let mut cons_bb = self.context.append_basic_block(parent, "cons");
        let mut alt_bb = self.context.append_basic_block(parent, "alt");
        let merge_bb = self.context.append_basic_block(parent, "merge");

        // Emits the entry conditional branch instructions, although we don't
        // need to capture it
        self.builder
            .build_conditional_branch(cond_bool, cons_bb, alt_bb);

        // Point the builder at the end of the empty cons block
        self.builder.position_at_end(cons_bb);
        // Gen IR for the cons block
        let cons_ir = self.gen_expr_ir(cons)?;
        // Make sure the consequent returns to the merge block after execution
        self.builder.build_unconditional_branch(merge_bb);
        // Update cons_bb in case the gen_expr_ir() moved it
        cons_bb = self.builder.get_insert_block().unwrap();

        // Point the builder at the end of the empty alt block
        self.builder.position_at_end(alt_bb);
        // Gen IR for the cons block
        let alt_ir = self.gen_expr_ir(alt.as_ref().unwrap())?;
        // Make sure the alternative returns to the merge block after execution
        self.builder.build_unconditional_branch(merge_bb);
        // Update alt_bb in case the gen_expr_ir() moved it
        alt_bb = self.builder.get_insert_block().unwrap();

        // Point the builder at the end of the empty merge block
        self.builder.position_at_end(merge_bb);
        // Create the phi node and insert code/value pairs
        let phi = self.builder.build_phi(self.context.f64_type(), "condtmp");
        phi.add_incoming(&[(&cons_ir, cons_bb), (&alt_ir, alt_bb)]);

        Ok(phi.as_basic_value().into_float_value())
    }
}
