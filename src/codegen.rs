use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::passes::PassManager;
use inkwell::types::BasicMetadataTypeEnum;
use inkwell::values::{BasicValue, FunctionValue, IntValue, PointerValue};
use inkwell::IntPredicate;
use std::collections::HashMap;

use crate::ast::AstNode;
use crate::ast::Expression;
use crate::ast::Function;
use crate::ast::Prototype;
use crate::token::Symbol;

enum CgRetVal<'ctx> {
    Expr(IntValue<'ctx>),
    Func(FunctionValue<'ctx>),
}

type ExprCgResult<'ctx> = Result<IntValue<'ctx>, String>;
type FuncCgResult<'ctx> = Result<FunctionValue<'ctx>, String>;

pub(crate) struct CodeGen<'a, 'ctx> {
    context: &'ctx Context,
    builder: &'a Builder<'ctx>,
    module: &'a Module<'ctx>,
    fpm: &'a PassManager<FunctionValue<'ctx>>,
    local_vars: HashMap<String, PointerValue<'ctx>>,
}

impl<'a, 'ctx> CodeGen<'a, 'ctx> {
    pub(crate) fn new(
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

        CodeGen {
            context,
            builder,
            module,
            fpm,
            local_vars: values,
        }
    }

    // Iterate over all nodes and codegen. Optionally return a string (for
    // testing).
    pub(crate) fn run(&mut self, ast: &[AstNode]) -> Result<FunctionValue, String> {
        let mut main: Option<FunctionValue> = None;
        for node in ast {
            let code = match node {
                AstNode::Expr(expr) => CgRetVal::Expr(self.expr_codegen(expr)?),
                AstNode::Func(func) => CgRetVal::Func(self.func_codegen(func)?),
            };

            if let CgRetVal::Func(f) = code {
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

    fn proto_codegen(&self, proto: &Prototype) -> FuncCgResult<'ctx> {
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

    fn func_codegen(&mut self, func: &Function) -> FuncCgResult<'ctx> {
        let function = self.proto_codegen(&func.proto)?;
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
            last_expr = Some(Box::new(self.expr_codegen(e)?));
        }
        self.builder.build_return(last_expr.as_deref());

        // Make sure we didn't miss anything
        // TODO: Should this allow llvm to print, or use a verbose flag, or are
        // the errors not useful?
        if function.verify(true) {
            self.fpm.run_on(&function);
            Ok(function)
        } else {
            // unsafe {
            //     // TODO: Do we care about this for AOT comiplation?
            //     function.delete();
            // }
            Err(format!(
                "Error compiling: {}",
                function.get_name().to_str().unwrap()
            ))
        }
    }

    fn expr_codegen(&mut self, expr: &Expression) -> ExprCgResult<'ctx> {
        match expr {
            Expression::Num { value } => self.num_codegen(*value),
            Expression::Var { name } => self.var_codegen(name),
            Expression::BinOp { sym, lhs, rhs } => self.binop_codegen(sym, lhs, rhs),
            Expression::UnOp { sym, rhs } => self.unop_codegen(sym, rhs),
            Expression::Call { name, args } => self.call_codegen(name, args),
            Expression::Cond { cond, cons, alt } => self.cond_codegen(cond, cons, alt),
            Expression::For {
                var_name,
                start,
                cond,
                step,
                body,
            } => self.for_codegen(var_name, start, cond, step, body),
            Expression::Let { name, init } => self.let_codegen(name, init),
        }
    }

    fn num_codegen(&self, num: u64) -> ExprCgResult<'ctx> {
        Ok(self.context.i64_type().const_int(num, false))
    }

    fn var_codegen(&self, name: &str) -> ExprCgResult<'ctx> {
        // Get the variable pointer and load from the stack
        match self.local_vars.get(name) {
            Some(var) => Ok(self.builder.build_load(*var, name).into_int_value()),
            None => Err(format!("Unknown variable: {}", name)),
        }
    }

    fn binop_codegen(
        &mut self,
        op: &Symbol,
        lhs: &Expression,
        rhs: &Expression,
    ) -> ExprCgResult<'ctx> {
        use super::token::Symbol::*;

        // If assignment, make sure lvalue is a variable and store rhs there
        if *op == Assign {
            let l_var = match lhs {
                Expression::Var { name } => name,
                _ => return Err("Expected LHS to be a variable for assignment".to_string()),
            };

            let r_val = self.expr_codegen(rhs)?;
            let l_var = self
                .local_vars
                .get(l_var)
                .ok_or(format!("Unknown variable in assignment: {}", l_var))?
                .to_owned();

            self.builder.build_store(l_var, r_val);

            return Ok(r_val);
        }

        let lhs = self.expr_codegen(lhs)?;
        let rhs = self.expr_codegen(rhs)?;

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
                    _ => return Err("Something went really wrong in binop_codegen()".to_string()),
                };
                // Convert the i1 to a double
                Ok(cmp)
            }
            op @ (Gt | Lt | Eq) => {
                let pred = match op {
                    Gt => IntPredicate::UGT,
                    Lt => IntPredicate::ULT,
                    Eq => IntPredicate::EQ,
                    _ => return Err("Something went really wrong in binop_codegen()".to_string()),
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

    fn call_codegen(&mut self, name: &str, args: &[Expression]) -> ExprCgResult<'ctx> {
        let func = self
            .module
            .get_function(name)
            .ok_or(format!("Unknown function call: {}", name))?;

        let mut args_code = Vec::with_capacity(args.len());
        for arg in args {
            args_code.push(self.expr_codegen(arg)?.into());
        }

        match self
            .builder
            .build_call(func, &args_code, "tmpcall")
            .try_as_basic_value()
            .left()
        {
            Some(v) => Ok(v.into_int_value()),
            None => Err(String::from("Invalid call?")),
        }
    }

    // if then optional else
    fn cond_codegen(
        &mut self,
        cond_expr: &Expression,
        then_expr: &[Expression],
        else_expr: &Option<Vec<Expression>>, // todo: can this be a slice?
    ) -> ExprCgResult<'ctx> {
        // Get the current function for insertion
        let parent = self
            .builder
            .get_insert_block()
            .and_then(|x| x.get_parent())
            .ok_or("Parent function not found when building conditional")?;

        // CodeGen expression. Will be optimized to a 0 or 1 if comparing
        // constants. Otherwise, the value will be IR to evaluate. Result will
        // be a float 0 or 1.
        let cond_val = self.expr_codegen(cond_expr)?;

        // Codegen to compare the cond_code (0 or 1) to 0. Result will be a 1 bit
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

        // CodeGen the then block
        for expr in then_expr {
            self.expr_codegen(expr)?;
        }

        // Make sure the consequent returns to the end block after execution
        self.builder.build_unconditional_branch(end_block);

        // Point the builder at the end of the empty else block
        self.builder.position_at_end(else_block);

        if else_expr.is_some() {
            // CodeGen the else block
            for expr in else_expr.as_ref().unwrap() {
                self.expr_codegen(expr)?;
            }

            // Make sure the alternative returns to the end block after execution
            self.builder.build_unconditional_branch(end_block);

            // Point the builder at the end of the empty end block
            self.builder.position_at_end(end_block);
        }

        Ok(self.context.i64_type().const_zero())
    }

    /* CodeGen for conditionals. IR roughly looks like:
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
    fn cond_codegen_phi(
        &mut self,
        cond: &Expression,
        cons: &[Expression],
        alt: &Option<Vec<Expression>>, // todo: can this be a slice?
    ) -> ExprCgResult<'ctx> {
        // Get the current function for insertion
        let parent = self
            .builder
            .get_insert_block()
            .and_then(|x| x.get_parent())
            .ok_or("Parent function not found when building conditional")?;

        // CodeGen cond expression. Will be optimized to a 0 or 1 if comparing
        // constants. Otherwise, the value will be IR to evaluate. Result will
        // be a float 0.0 or 1.0.
        let cond_code = self.expr_codegen(cond)?;

        // CodeGen to compare the cond_code (0 or 1) to 0. Result will be a 1 bit
        // "bool".
        let cond_bool = self.builder.build_int_compare(
            IntPredicate::NE,
            cond_code,
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
        // CodeGen the cons block
        let mut cons_code: Option<IntValue> = None; // todo: this is aweful
        for expr in cons {
            cons_code = Some(self.expr_codegen(expr)?);
        }

        // Make sure the consequent returns to the merge block after execution
        self.builder.build_unconditional_branch(merge_bb);
        // Update cons_bb in case the expr_codegen() moved it
        cons_bb = self.builder.get_insert_block().unwrap();

        // Point the builder at the end of the empty alt block
        self.builder.position_at_end(alt_bb);
        // CodeGen for the alt block
        let mut alt_code: Option<IntValue> = None;
        for expr in alt.as_ref().unwrap() {
            alt_code = Some(self.expr_codegen(expr)?);
        }
        // Make sure the alternative returns to the merge block after execution
        self.builder.build_unconditional_branch(merge_bb);
        // Update alt_bb in case the expr_codegen() moved it
        alt_bb = self.builder.get_insert_block().unwrap();

        // Point the builder at the end of the empty merge block
        self.builder.position_at_end(merge_bb);
        // Create the phi node and insert code/value pairs
        let phi = self.builder.build_phi(self.context.i64_type(), "condtmp");
        phi.add_incoming(&[(&cons_code.unwrap(), cons_bb), (&alt_code.unwrap(), alt_bb)]);

        Ok(phi.as_basic_value().into_int_value())
    }

    // for start; cond; step { body }
    // start == let var_name = x
    fn for_codegen(
        &mut self,
        var_name: &str,
        start: &Expression,
        cond: &Expression,
        step: &Expression,
        body: &[Expression],
    ) -> ExprCgResult<'ctx> {
        let parent = self
            .builder
            .get_insert_block()
            .and_then(|x| x.get_parent())
            .ok_or("Parent function not found when building loop")?;

        // Create entry alloca, codegen start expr, and store result
        let start_alloca = self.create_entry_block_alloca(var_name, &parent);
        let start_code = self.expr_codegen(start)?;
        self.builder.build_store(start_alloca, start_code);

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
            self.expr_codegen(expr)?;
        }

        // Codegen step value and end cond
        let step_code = self.expr_codegen(step)?;
        let cond_code = self.expr_codegen(cond)?;

        // Load the current induction variable from the stack, increment it by
        // step, and store it again. Body could have mutated it.
        let cur = self.builder.build_load(start_alloca, var_name);
        let next = self
            .builder
            .build_int_add(cur.into_int_value(), step_code, "incvar");
        self.builder.build_store(start_alloca, next);

        let cond_bool = self.builder.build_int_compare(
            IntPredicate::NE,
            cond_code,
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

    fn unop_codegen(&mut self, op: &Symbol, rhs: &Expression) -> ExprCgResult<'ctx> {
        use Symbol::*;

        let rhs = self.expr_codegen(rhs)?;
        match op {
            Minus => Ok(self.builder.build_int_neg(rhs, "neg")),
            x => Err(format!("Unknown unary operator: {}", x)),
        }
    }

    fn let_codegen(&mut self, name: &str, init: &Option<Box<Expression>>) -> ExprCgResult<'ctx> {
        let parent = self
            .builder
            .get_insert_block()
            .and_then(|x| x.get_parent())
            .ok_or("Parent function not found when building let expression")?;

        let init_code = match init {
            Some(init) => self.expr_codegen(init)?,
            None => self.context.i64_type().const_zero(),
        };

        let init_alloca = self.create_entry_block_alloca(name, &parent);
        self.builder.build_store(init_alloca, init_code);

        self.local_vars.insert(name.to_owned(), init_alloca);

        Ok(init_code)
    }
}

#[cfg(test)]
mod test {
    use inkwell::passes::PassManager;
    use inkwell::values::FunctionValue;
    use inkwell::{context::Context, values::AnyValue};
    use insta::{assert_yaml_snapshot, glob, with_settings};
    use std::fs;

    use super::*;
    use crate::lexer::Lexer;
    use crate::parser::Parser;

    // This is how we "deserialize" FunctionValue to work with insta
    fn code_to_string(code: Result<FunctionValue, String>) -> String {
        match code {
            Ok(code) => code.print_to_string().to_string(),
            Err(err) => err,
        }
    }

    #[test]
    fn test_codegen() {
        with_settings!({ snapshot_path => "tests/snapshots", prepend_module_to_snapshot => false }, {
            glob!("tests/inputs/codegen/*.input", |path| {
                let input = fs::read_to_string(path).unwrap();
                let tokens = Lexer::new(&input).collect::<Result<Vec<_>, _>>().unwrap();
                let parser = Parser::new(&tokens);
                let ast = parser.parse().unwrap();

                let context = Context::create();
                let builder = context.create_builder();
                let module = context.create_module("main_mod");
                let fpm = PassManager::create(&module);
                let mut codegen = CodeGen::new(&context, &builder, &module, &fpm);

                assert_yaml_snapshot!(code_to_string(codegen.run(&ast)));
            });
        });
    }
}