use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::passes::PassManager;
use inkwell::types::BasicMetadataTypeEnum;
use inkwell::values::{AnyValueEnum, BasicValue, FloatValue, FunctionValue, PointerValue};
use inkwell::FloatPredicate;
use std::cell::RefCell;
use std::collections::HashMap;

use crate::lexer::Symbol;
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
    values: RefCell<HashMap<String, AnyValueEnum<'ctx>>>,
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
            values: RefCell::new(values),
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

        // Create a function type depending on args types and return type
        let func_type = f64_type.fn_type(&args_type, false);
        // Add function to current module's symbold table. Defaults to external
        // linkage with None.
        let func = self.module.add_function(&proto.name, func_type, None);

        // Name all args
        func.get_param_iter().enumerate().for_each(|(i, arg)| {
            arg.into_float_value().set_name(&proto.args[i]);
        });

        Ok(func)
    }

    fn gen_func_ir(&mut self, func: &Function) -> FuncIrResult<'ctx> {
        let function = self.gen_proto_ir(&func.proto)?;
        // If body is None assume call is an extern
        let body = match func.body.as_ref() {
            Some(body) => body,
            None => return Ok(function),
        };

        // Create new block for function
        let bb = self.context.append_basic_block(function, "entry");
        // Make sure the builder will insert new instructions at the end
        self.builder.position_at_end(bb);

        self.values.borrow_mut().clear();
        for (i, arg) in function.get_param_iter().enumerate() {
            self.values.borrow_mut().insert(func.proto.args[i].clone(), arg.into());
        }

        //todo: no redefining functions

        // Generate and add all expressions in the body. Save the last to
        // one to use with the ret instruction.
        let mut last_expr: Option<Box<dyn BasicValue>> = None;
        for e in body {
            last_expr = Some(Box::new(self.gen_expr_ir(e)?));
        }
        self.builder.build_return(last_expr.as_deref());

        // Make sure we didn't miss anything
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
            Expression::Num { value } => self.gen_num_ir(*value),
            Expression::Var { name } => self.gen_var_ir(name),
            Expression::BinOp { sym, lhs, rhs } => self.gen_binop_ir(sym, lhs, rhs),
            Expression::UnOp { sym, rhs } => self.gen_unop_ir(sym, rhs),
            Expression::Call { name, args } => self.gen_call_ir(name, args),
            Expression::Cond { cond, cons, alt } => self.gen_cond_ir(cond, cons, alt),
            Expression::For {
                var_name,
                start,
                cond,
                step,
                body,
            } => self.gen_for_ir(var_name, start, cond, step, body),
        }
    }

    fn gen_num_ir(&self, num: f64) -> ExprIrResult<'ctx> {
        Ok(self.context.f64_type().const_float(num))
    }

    fn gen_var_ir(&self, name: &str) -> ExprIrResult<'ctx> {
        match self.values.borrow().get(name) {
            Some(var) => {
                let var = match var {
                    AnyValueEnum::FloatValue(f) => *f,
                    AnyValueEnum::PhiValue(v) => v.as_basic_value().into_float_value(),
                    AnyValueEnum::PointerValue(p) => {
                        self.builder.build_load(*p, name).into_float_value()
                    }
                    _ => unimplemented!("Unknown variable type"),
                };
                Ok(var)
            }
            None => Err(format!("Unknown variable: {}", name)),
        }
    }

    fn gen_binop_ir(&self, op: &Symbol, lhs: &Expression, rhs: &Expression) -> ExprIrResult<'ctx> {
        use Symbol::*;

        let lhs = self.gen_expr_ir(lhs)?;
        let rhs = self.gen_expr_ir(rhs)?;

        // Generate the proper instruction for each op
        match op {
            Mult => Ok(self.builder.build_float_mul(lhs, rhs, "tmpmul")),
            Div => Ok(self.builder.build_float_div(lhs, rhs, "tmpdiv")),
            Plus => Ok(self.builder.build_float_add(lhs, rhs, "tmpadd")),
            Minus => Ok(self.builder.build_float_sub(lhs, rhs, "tmpsub")),
            op @ (And | Or) => {
                let lhs = self.builder.build_float_to_signed_int(
                    lhs,
                    self.context.i64_type(),
                    "tmplhsint",
                );
                let rhs = self.builder.build_float_to_signed_int(
                    rhs,
                    self.context.i64_type(),
                    "tmprhsint",
                );
                let cmp = match op {
                    And => self.builder.build_and(lhs, rhs, "tmpand"),
                    Or => self.builder.build_or(lhs, rhs, "tmpor"),
                    _ => return Err("Something went really wrong in gen_binop_ir()".to_string()),
                };
                // Convert the i1 to a double
                Ok(self.builder.build_unsigned_int_to_float(
                    cmp,
                    self.context.f64_type(),
                    "tmpbool",
                ))
            }
            op @ (Gt | Lt | Eq) => {
                let pred = match op {
                    Gt => FloatPredicate::UGT,
                    Lt => FloatPredicate::ULT,
                    Eq => FloatPredicate::UEQ,
                    _ => return Err("Something went really wrong in gen_binop_ir()".to_string()),
                };
                let cmp = self.builder.build_float_compare(pred, lhs, rhs, "tmpcmp");
                // Convert the i1 to a double
                Ok(self.builder.build_unsigned_int_to_float(
                    cmp,
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

        // Gen cond expression IR. Will be optimized to a 0 or 1 if comparing
        // constants. Otherwise, the value will be IR to evaluate. Result will
        // be a float 0.0 or 1.0.
        let cond_ir = self.gen_expr_ir(cond)?;

        // Gen IR to compare the cond_ir (0 or 1) to 0. Result will be a 1 bit
        // "bool".
        let cond_bool = self.builder.build_float_compare(
            FloatPredicate::ONE,
            cond_ir,
            self.context.f64_type().const_float(0.0),
            "ifcond",
        );

        // Create blocks for branches and after (phi)
        let mut cons_bb = self.context.append_basic_block(parent, "cons");
        let mut alt_bb = self.context.append_basic_block(parent, "alt");
        let merge_bb = self.context.append_basic_block(parent, "merge");

        // Emits the entry conditional branch instructions
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

    fn gen_for_ir(
        &self,
        var_name: &str,
        start: &Expression,
        cond: &Expression,
        step: &Expression,
        body: &[Expression],
    ) -> ExprIrResult<'ctx> {
        let parent = self
            .builder
            .get_insert_block()
            .and_then(|x| x.get_parent())
            .ok_or("Parent function not found when building loop")?;

        let start_ir = self.gen_expr_ir(start)?;

        // Get the block that will fall through to the loop
        let pre_bb = self.builder.get_insert_block().unwrap();
        // Create a block for the loop
        let loop_bb = self.context.append_basic_block(parent, "loop");
        // Create a branch to the loop
        self.builder.build_unconditional_branch(loop_bb);
        // Move the insertion point
        self.builder.position_at_end(loop_bb);
        // Create a phi node for the loop variable
        let loop_var = self.builder.build_phi(self.context.f64_type(), var_name);
        // Add the variable to the node. This means if we come from `pre_bb` set
        // it to the start value.
        loop_var.add_incoming(&[(&start_ir, pre_bb)]);

        // Save the variable value if we are shadowing
        let old_var = self.values.borrow_mut().remove(var_name);
        // Insert the phi as a pointer value
        self.values
            .borrow_mut()
            .insert(var_name.to_owned(), AnyValueEnum::PhiValue(loop_var));

        // Generate all body expression
        for expr in body {
            self.gen_expr_ir(expr)?;
        }

        // Step value: loop_var + step
        let step_ir = self.gen_expr_ir(step)?;
        let next_var_ir = self.builder.build_float_add(
            loop_var.as_basic_value().into_float_value(),
            step_ir,
            "nextvar",
        );

        // Loop end cond bool
        let cond_ir = self.gen_expr_ir(cond)?;
        let cond_bool = self.builder.build_float_compare(
            FloatPredicate::ONE,
            cond_ir,
            self.context.f64_type().const_float(0.0),
            "loopcond",
        );

        // Remember the last block for the phi node
        let loop_end_bb = self.builder.get_insert_block().unwrap();
        // Block for after the loop
        let after_bb = self.context.append_basic_block(parent, "afterloop");
        // Insert the loop conditional at the end
        self.builder
            .build_conditional_branch(cond_bool, loop_bb, after_bb);
        // Advance to after after_bb
        self.builder.position_at_end(after_bb);

        // Complete the phi node. This means if we come from `loop_end_bb` set
        // it to the next loop value.
        loop_var.add_incoming(&[(&next_var_ir, loop_end_bb)]);

        // Reset shadowed variable
        self.values.borrow_mut().remove(var_name);
        if let Some(v) = old_var {
            self.values.borrow_mut().insert(var_name.to_owned(), v);
        }

        Ok(self.context.f64_type().const_float(0.0))
    }

    fn gen_unop_ir(&self, op: &Symbol, rhs: &Expression) -> ExprIrResult<'ctx> {
        use Symbol::*;

        let rhs = self.gen_expr_ir(rhs)?;
        match op {
            Minus => Ok(self.builder.build_float_neg(rhs, "neg")),
            x => Err(format!("Unknown unary operator: {}", x)),
        }
    }
}
