use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::passes::PassManager;
use inkwell::types::BasicMetadataTypeEnum;
use inkwell::values::{BasicValue, FunctionValue, IntValue, PointerValue};
use inkwell::IntPredicate;
use std::collections::HashMap;

use crate::lexer::Symbol;
use crate::parser::AstNode;
use crate::parser::Expression;
use crate::parser::Function;
use crate::parser::Prototype;

enum IrRetVal<'ctx> {
    Expr(IntValue<'ctx>),
    Func(FunctionValue<'ctx>),
}

type ExprIrResult<'ctx> = Result<IntValue<'ctx>, String>;
type FuncIrResult<'ctx> = Result<FunctionValue<'ctx>, String>;

pub struct IrGenerator<'a, 'ctx> {
    context: &'ctx Context,
    builder: &'a Builder<'ctx>,
    module: &'a Module<'ctx>,
    fpm: &'a PassManager<FunctionValue<'ctx>>,
    local_vars: HashMap<String, PointerValue<'ctx>>,
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
        fpm.add_basic_alias_analysis_pass();
        fpm.add_promote_memory_to_register_pass();
        fpm.add_instruction_combining_pass();
        fpm.add_reassociate_pass();
        fpm.initialize();

        IrGenerator {
            context,
            builder,
            module,
            fpm,
            local_vars: values,
        }
    }

    // Helper to create an alloca in the entry block for local variables
    fn create_entry_block_alloca(&self, name: &str, func: &FunctionValue) -> PointerValue<'ctx> {
        // Create a temporary builder
        let builder = self.context.create_builder();

        // Get the first block of the current function
        let entry = func.get_first_basic_block().unwrap();

        // Rewind to the first instruction and insert before it or at the end if
        // empty
        match entry.get_first_instruction() {
            Some(inst) => builder.position_before(&inst),
            None => builder.position_at_end(entry),
        }

        // Create alloca and return it
        builder.build_alloca(self.context.i64_type(), name)
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
        let i64_type = self.context.i64_type();
        let args_type = proto
            .args
            .iter()
            .map(|_| i64_type.into())
            .collect::<Vec<BasicMetadataTypeEnum>>();

        // Create a function type depending on args types and return type
        let func_type = i64_type.fn_type(&args_type, false);
        // Add function to current module's symbold table. Defaults to external
        // linkage with None.
        let func = self.module.add_function(&proto.name, func_type, None);

        // Name all args
        func.get_param_iter().enumerate().for_each(|(i, arg)| {
            arg.into_int_value().set_name(&proto.args[i]);
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

        // Allocate space for the function's arguments on the stack
        self.local_vars.reserve(func.proto.args.len());
        for (i, arg) in function.get_param_iter().enumerate() {
            let alloca = self.create_entry_block_alloca(&func.proto.args[i], &function);
            self.builder.build_store(alloca, arg);
            self.local_vars
                .insert(func.proto.args[i].to_owned(), alloca);
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

    fn gen_expr_ir(&mut self, expr: &Expression) -> ExprIrResult<'ctx> {
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
            Expression::Let { name, init } => self.gen_let_ir(name, init),
        }
    }

    fn gen_num_ir(&self, num: u64) -> ExprIrResult<'ctx> {
        Ok(self.context.i64_type().const_int(num, false))
    }

    fn gen_var_ir(&self, name: &str) -> ExprIrResult<'ctx> {
        // Get the variable pointer and load from the stack
        match self.local_vars.get(name) {
            Some(var) => Ok(self.builder.build_load(*var, name).into_int_value()),
            None => Err(format!("Unknown variable: {}", name)),
        }
    }

    fn gen_binop_ir(
        &mut self,
        op: &Symbol,
        lhs: &Expression,
        rhs: &Expression,
    ) -> ExprIrResult<'ctx> {
        use Symbol::*;

        // If assignment, make sure lvalue is a variable and store rhs there
        if *op == Assign {
            let l_var = match lhs {
                Expression::Var { name } => name,
                _ => return Err("Expected LHS to be a variable for assignment".to_string()),
            };

            let r_val = self.gen_expr_ir(rhs)?;
            let l_var = self
                .local_vars
                .get(l_var)
                .ok_or(format!("Unknown variable in assignment: {}", l_var))?
                .to_owned();

            self.builder.build_store(l_var, r_val);

            return Ok(r_val);
        }

        let lhs = self.gen_expr_ir(lhs)?;
        let rhs = self.gen_expr_ir(rhs)?;

        // Generate the proper instruction for each op
        match op {
            Mult => Ok(self.builder.build_int_mul(lhs, rhs, "tmpmul")),
            Div => Ok(self.builder.build_int_unsigned_div(lhs, rhs, "tmpdiv")),
            Plus => Ok(self.builder.build_int_add(lhs, rhs, "tmpadd")),
            Minus => Ok(self.builder.build_int_sub(lhs, rhs, "tmpsub")),
            op @ (And | Or) => {
                // let lhs = self.builder.build_float_to_signed_int(
                //     lhs,
                //     self.context.i64_type(),
                //     "tmplhsint",
                // );
                // let rhs = self.builder.build_float_to_signed_int(
                //     rhs,
                //     self.context.i64_type(),
                //     "tmprhsint",
                // );
                let cmp = match op {
                    And => self.builder.build_and(lhs, rhs, "tmpand"),
                    Or => self.builder.build_or(lhs, rhs, "tmpor"),
                    _ => return Err("Something went really wrong in gen_binop_ir()".to_string()),
                };
                // Convert the i1 to a double
                Ok(cmp)
            }
            op @ (Gt | Lt | Eq) => {
                let pred = match op {
                    Gt => IntPredicate::UGT,
                    Lt => IntPredicate::ULT,
                    Eq => IntPredicate::EQ,
                    _ => return Err("Something went really wrong in gen_binop_ir()".to_string()),
                };
                let cmp = self.builder.build_int_compare(pred, lhs, rhs, "tmpcmp");
                // Convert the i1 to a double
                Ok(self
                    .builder
                    .build_int_cast(cmp, self.context.i64_type(), "tmpbool"))
            }
            x => Err(format!("Unknown binary operator: {}", x)),
        }
    }

    fn gen_call_ir(&mut self, name: &str, args: &[Expression]) -> ExprIrResult<'ctx> {
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
            Some(v) => Ok(v.into_int_value()),
            None => Err(String::from("Invalid call?")),
        }
    }

    // if then optional else
    fn gen_cond_ir(
        &mut self,
        cond_expr: &Expression,
        then_expr: &[Expression],
        else_expr: &Option<Vec<Expression>>, // todo: can this be a slice?
    ) -> ExprIrResult<'ctx> {
        // Get the current function for insertion
        let parent = self
            .builder
            .get_insert_block()
            .and_then(|x| x.get_parent())
            .ok_or("Parent function not found when building conditional")?;

        // Gen cond expression IR. Will be optimized to a 0 or 1 if comparing
        // constants. Otherwise, the value will be IR to evaluate. Result will
        // be a float 0 or 1.
        let cond_val = self.gen_expr_ir(cond_expr)?;

        // Gen IR to compare the cond_ir (0 or 1) to 0. Result will be a 1 bit
        // "bool".
        let cond_bool = self.builder.build_int_compare(
            IntPredicate::NE,
            cond_val,
            self.context.i64_type().const_zero(),
            "if.cond",
        );

        // Create blocks for branches and after. The else block is just a
        // pointer to end if there's no else expression.
        let then_block = self.context.append_basic_block(parent, "if.then");
        let end_block = self.context.append_basic_block(parent, "if.end");
        let mut else_block = end_block;
        if else_expr.is_some() {
            else_block = self.context.append_basic_block(parent, "if.else");
            else_block
                .move_before(end_block)
                .map_err(|_| String::from("LLVM error"))?;
        }

        // Emits the entry conditional branch instructions
        self.builder
            .build_conditional_branch(cond_bool, then_block, else_block);

        // Point the builder at the end of the empty then block
        self.builder.position_at_end(then_block);

        // Gen IR for the then block
        for expr in then_expr {
            self.gen_expr_ir(expr)?;
        }

        // Make sure the consequent returns to the end block after execution
        self.builder.build_unconditional_branch(end_block);

        // Point the builder at the end of the empty else block
        self.builder.position_at_end(else_block);

        if else_expr.is_some() {
            // Gen IR for the else block
            for expr in else_expr.as_ref().unwrap() {
                self.gen_expr_ir(expr)?;
            }

            // Make sure the alternative returns to the end block after execution
            self.builder.build_unconditional_branch(end_block);

            // Point the builder at the end of the empty end block
            self.builder.position_at_end(end_block);
        }

        Ok(self.context.i64_type().const_zero())
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
    // Keeping as an example of using phi
    #[allow(dead_code)]
    fn gen_cond_ir_phi(
        &mut self,
        cond: &Expression,
        cons: &[Expression],
        alt: &Option<Vec<Expression>>, // todo: can this be a slice?
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
        let cond_bool = self.builder.build_int_compare(
            IntPredicate::NE,
            cond_ir,
            self.context.i64_type().const_zero(),
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
        let mut cons_ir: Option<IntValue> = None; // todo: this is aweful
        for expr in cons {
            cons_ir = Some(self.gen_expr_ir(expr)?);
        }

        // Make sure the consequent returns to the merge block after execution
        self.builder.build_unconditional_branch(merge_bb);
        // Update cons_bb in case the gen_expr_ir() moved it
        cons_bb = self.builder.get_insert_block().unwrap();

        // Point the builder at the end of the empty alt block
        self.builder.position_at_end(alt_bb);
        // Gen IR for the alt block
        let mut alt_ir: Option<IntValue> = None;
        for expr in alt.as_ref().unwrap() {
            alt_ir = Some(self.gen_expr_ir(expr)?);
        }
        // Make sure the alternative returns to the merge block after execution
        self.builder.build_unconditional_branch(merge_bb);
        // Update alt_bb in case the gen_expr_ir() moved it
        alt_bb = self.builder.get_insert_block().unwrap();

        // Point the builder at the end of the empty merge block
        self.builder.position_at_end(merge_bb);
        // Create the phi node and insert code/value pairs
        let phi = self.builder.build_phi(self.context.i64_type(), "condtmp");
        phi.add_incoming(&[(&cons_ir.unwrap(), cons_bb), (&alt_ir.unwrap(), alt_bb)]);

        Ok(phi.as_basic_value().into_int_value())
    }

    // for start; cond; step { body }
    // start == let var_name = x
    fn gen_for_ir(
        &mut self,
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

        // Create entry alloca, generate start expr IR, and store result
        let start_alloca = self.create_entry_block_alloca(var_name, &parent);
        let start_ir = self.gen_expr_ir(start)?;
        self.builder.build_store(start_alloca, start_ir);

        // Create a block for the loop, a branch to it, and move the insertion
        // to it
        let loop_bb = self.context.append_basic_block(parent, "loop");
        self.builder.build_unconditional_branch(loop_bb);
        self.builder.position_at_end(loop_bb);

        // Save the variable value if we are shadowing and insert alloca into
        // local map
        let old_var = self.local_vars.remove(var_name);
        self.local_vars.insert(var_name.to_owned(), start_alloca);

        // Generate all body expressions
        for expr in body {
            self.gen_expr_ir(expr)?;
        }

        // Generate step value and end cond IR
        let step_ir = self.gen_expr_ir(step)?;
        let cond_ir = self.gen_expr_ir(cond)?;

        // Load the current induction variable from the stack, increment it by
        // step, and store it again. Body could have mutated it.
        let cur = self.builder.build_load(start_alloca, var_name);
        let next = self
            .builder
            .build_int_add(cur.into_int_value(), step_ir, "incvar");
        self.builder.build_store(start_alloca, next);

        let cond_bool = self.builder.build_int_compare(
            IntPredicate::NE,
            cond_ir,
            self.context.i64_type().const_zero(),
            "endcond",
        );

        // Append a block for after the loop and insert the loop conditional at
        // the end
        let after_bb = self.context.append_basic_block(parent, "afterloop");
        self.builder
            .build_conditional_branch(cond_bool, loop_bb, after_bb);
        self.builder.position_at_end(after_bb);

        // Reset shadowed variable
        self.local_vars.remove(var_name);
        if let Some(v) = old_var {
            self.local_vars.insert(var_name.to_owned(), v);
        }

        Ok(self.context.i64_type().const_zero())
    }

    fn gen_unop_ir(&mut self, op: &Symbol, rhs: &Expression) -> ExprIrResult<'ctx> {
        use Symbol::*;

        let rhs = self.gen_expr_ir(rhs)?;
        match op {
            Minus => Ok(self.builder.build_int_neg(rhs, "neg")),
            x => Err(format!("Unknown unary operator: {}", x)),
        }
    }

    fn gen_let_ir(&mut self, name: &str, init: &Option<Box<Expression>>) -> ExprIrResult<'ctx> {
        let parent = self
            .builder
            .get_insert_block()
            .and_then(|x| x.get_parent())
            .ok_or("Parent function not found when building let expression")?;

        let init_ir = match init {
            Some(init) => self.gen_expr_ir(init)?,
            None => self.context.i64_type().const_zero(),
        };

        let init_alloca = self.create_entry_block_alloca(name, &parent);
        self.builder.build_store(init_alloca, init_ir);

        self.local_vars.insert(name.to_owned(), init_alloca);

        Ok(init_ir)
    }
}
