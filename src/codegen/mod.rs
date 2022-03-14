use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::passes::PassManager;
use inkwell::types::{BasicMetadataTypeEnum, BasicTypeEnum};
use inkwell::values::{BasicValue, BasicValueEnum, FunctionValue, PointerValue};
use inkwell::IntPredicate;
use std::collections::HashMap;

use crate::ast::Prototype;
use crate::ast::{Ast, Expression};
use crate::ast::{Node, Statement};
use crate::codegen::convert::AsExpr;
use crate::token::{Symbol, Type};

mod convert;

enum CgRetVal<'ctx> {
    Stmt(()),
    Expr(BasicValueEnum<'ctx>),
}

type StmtCgResult<'ctx> = Result<(), String>;
type ExprCgResult<'ctx> = Result<BasicValueEnum<'ctx>, String>;

macro_rules! extract_type {
    ($ctx:expr, $var:expr) => {{
        let (_, ty) = $var;
        match ty {
            Type::U64 => BasicMetadataTypeEnum::IntType($ctx.i64_type()),
            Type::F64 => BasicMetadataTypeEnum::FloatType($ctx.f64_type()),
            Type::I64 => todo!("proto var"),
        }
    }};
}

pub(crate) struct CodeGen<'a, 'ctx> {
    context: &'ctx Context,
    builder: &'a Builder<'ctx>,
    module: &'a Module<'ctx>,
    fpm: &'a PassManager<FunctionValue<'ctx>>,
    local_vars: HashMap<String, PointerValue<'ctx>>,
    main: Option<FunctionValue<'ctx>>,
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
            main: None,
        }
    }

    // Iterate over all nodes and codegen. Optionally return a string (for
    // testing).
    pub(crate) fn walk(&mut self, ast: &Ast) -> Result<FunctionValue, String> {
        for node in ast.nodes() {
            match node {
                Node::Stmt(stmt) => CgRetVal::Stmt(self.stmt_codegen(stmt)?),
                Node::Expr(expr) => CgRetVal::Expr(self.expr_codegen(expr)?),
            };
        }
        self.main.ok_or_else(|| "main() not found".to_string())
    }

    // Helper to create an alloca in the entry block for local variables
    fn create_entry_block_alloca(
        &self,
        (name, ty): (&str, Type),
        func: &FunctionValue,
    ) -> PointerValue<'ctx> {
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
        match ty {
            Type::I64 => todo!("alloca"),
            Type::U64 => builder.build_alloca(self.context.i64_type(), name),
            Type::F64 => builder.build_alloca(self.context.f64_type(), name),
        }
    }

    fn stmt_codegen(&mut self, expr: &Statement) -> StmtCgResult<'ctx> {
        use Statement::*;
        match expr {
            Cond { cond, cons, alt } => {
                self.cond_codegen(cond.as_expr()?, &*cons.as_expr()?, &alt.as_expr()?)
            }
            For {
                var_name,
                start,
                cond,
                step,
                body,
            } => self.for_codegen(var_name, start, cond, step, body),
            Let { name, ty, init } => self.let_codegen(name, *ty, &init.as_expr()?),
            Fn { proto, body } => self.func_codegen(proto, body),
        }
    }

    fn proto_codegen(&self, proto: &Prototype) -> Result<FunctionValue<'ctx>, String> {
        let args_type = proto
            .args
            .iter()
            .map(|x| extract_type!(self.context, x))
            .collect::<Vec<BasicMetadataTypeEnum>>();

        println!(">>>{:?}", proto.name);
        // Create a function type depending on args types and return type
        let func_type = match args_type.get(0) {
            Some(BasicMetadataTypeEnum::FloatType(_)) => {
                self.context.f64_type().fn_type(&args_type, false) // XXX
            }
            None | Some(BasicMetadataTypeEnum::IntType(_)) => {
                self.context.i64_type().fn_type(&args_type, false)
            }
            _ => todo!("ret type"),
        };

        // Add function to current module's symbold table. Defaults to external
        // linkage with None.
        let func = self.module.add_function(&proto.name, func_type, None);

        // Name all args
        func.get_param_iter().enumerate().for_each(|(i, arg)| {
            arg.set_name(&proto.args[i].0);
        });

        Ok(func)
    }

    fn func_codegen(&mut self, proto: &Prototype, body: &Option<Vec<Node>>) -> StmtCgResult<'ctx> {
        let function = self.proto_codegen(proto)?;
        // If body is None assume call is an extern
        let body = match body {
            Some(body) => body,
            None => return Ok(()),
        };

        // Create new block for function
        let bb = self.context.append_basic_block(function, "entry");
        // Make sure the builder will insert new instructions at the end
        self.builder.position_at_end(bb);

        // Allocate space for the function's arguments on the stack
        self.local_vars.reserve(proto.args.len());
        for (i, arg) in function.get_param_iter().enumerate() {
            let (x, y) = &proto.args[i];
            let alloca = self.create_entry_block_alloca((x, *y), &function);
            self.builder.build_store(alloca, arg);
            self.local_vars.insert(proto.args[i].0.to_owned(), alloca);
        }

        //todo: no redefining functions

        // Generate and add all expressions in the body. Save the last to
        // one to use with the ret instruction.
        //let mut last_expr: Option<Box<dyn BasicValue>> = None;
        let mut last_expr: Option<&Node> = None;
        for e in body {
            println!(">>>{:?}", e);
            //last_expr = Some(Box::new(self.expr_codegen(e)?));
            last_expr = Some(e);
        }
        // todo: this makes the return type possibly clash with the proto return
        // type if a statement is last
        let last_expr: Option<Box<dyn BasicValue>> = match last_expr.unwrap() { // XXX
            Node::Stmt(_) => None,
            Node::Expr(e) => Some(Box::new(self.expr_codegen(e)?)),
        };
        self.builder.build_return(last_expr.as_deref());

        // Make sure we didn't miss anything
        // TODO: Should this allow llvm to print or use a verbose flag, or are
        // the errors not useful?
        if function.verify(true) {
            self.fpm.run_on(&function);

            if function.get_name().to_str().unwrap() == "main" {
                self.main = Some(function);
            }
            Ok(())
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
            Expression::U64(_) | Expression::F64(_) => self.num_codegen(expr),
            Expression::Var { name } => self.var_codegen(name),
            Expression::BinOp { sym, lhs, rhs } => {
                self.binop_codegen(*sym, lhs.as_expr()?, rhs.as_expr()?)
            }
            Expression::UnOp { sym, rhs } => self.unop_codegen(*sym, rhs.as_expr()?),
            Expression::Call { name, args } => self.call_codegen(name, &args.as_expr()?),
            x => todo!("8<>>>{}", x),
        }
    }

    fn num_codegen(&self, num: &Expression) -> ExprCgResult<'ctx> {
        Ok(match num {
            Expression::U64(n) => self
                .context
                .i64_type()
                .const_int(*n, true)
                .as_basic_value_enum(),
            Expression::F64(n) => self
                .context
                .f64_type()
                .const_float(*n)
                .as_basic_value_enum(),
            _ => todo!("num"),
        })
    }

    // fn num_codegen_i64(&self, num: u64) -> ExprCgResult<'ctx> {
    //     Ok(self.context.i64_type().const_int(num, false).as_basic_value_enum())
    // }

    // fn num_codegen_f64(&self, num: f64) -> ExprCgResult<'ctx> {
    //     Ok(self.context.f64_type().const_float(num).as_basic_value_enum())
    // }

    fn var_codegen(&self, name: &str) -> ExprCgResult<'ctx> {
        // Get the variable pointer and load from the stack
        match self.local_vars.get(name) {
            Some(var) => Ok(self.builder.build_load(*var, name)),
            None => Err(format!("Unknown variable: {}", name)),
        }
    }

    fn binop_codegen(
        &mut self,
        op: Symbol,
        lhs: &Expression,
        rhs: &Expression,
    ) -> ExprCgResult<'ctx> {
        use super::token::Symbol::*;

        // If assignment, make sure lvalue is a variable and store rhs there
        if op == Assign {
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
            Mult => Ok(self
                .builder
                .build_int_mul(lhs.into_int_value(), rhs.into_int_value(), "tmpmul")
                .as_basic_value_enum()),
            Div => Ok(self
                .builder
                .build_int_unsigned_div(lhs.into_int_value(), rhs.into_int_value(), "tmpdiv")
                .as_basic_value_enum()),
            Plus => Ok(match lhs.get_type() {
                BasicTypeEnum::ArrayType(_) => todo!("math"),
                BasicTypeEnum::FloatType(_) => self
                    .builder
                    .build_float_add(lhs.into_float_value(), rhs.into_float_value(), "floatadd")
                    .as_basic_value_enum(),
                BasicTypeEnum::IntType(_) => self
                    .builder
                    .build_int_add(lhs.into_int_value(), rhs.into_int_value(), "intadd")
                    .as_basic_value_enum(),
                BasicTypeEnum::PointerType(_) => todo!("math"),
                BasicTypeEnum::StructType(_) => todo!("math"),
                BasicTypeEnum::VectorType(_) => todo!("math"),
            }),
            Minus => Ok(self
                .builder
                .build_int_sub(lhs.into_int_value(), rhs.into_int_value(), "tmpsub")
                .as_basic_value_enum()),
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
                    And => self
                        .builder
                        .build_and(lhs.into_int_value(), rhs.into_int_value(), "tmpand")
                        .as_basic_value_enum(),
                    Or => self
                        .builder
                        .build_or(lhs.into_int_value(), rhs.into_int_value(), "tmpor")
                        .as_basic_value_enum(),
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
                let cmp = self.builder.build_int_compare(
                    pred,
                    lhs.into_int_value(),
                    rhs.into_int_value(),
                    "tmpcmp",
                );
                // Convert the i1 to a double
                Ok(self
                    .builder
                    .build_int_cast(cmp, self.context.i64_type(), "tmpbool")
                    .as_basic_value_enum())
            }
            x => Err(format!("Unknown binary operator: {}", x)),
        }
    }

    fn call_codegen(&mut self, name: &str, args: &[&Expression]) -> ExprCgResult<'ctx> {
        let func = self
            .module
            .get_function(name)
            .ok_or(format!("Unknown function call: {}", name))?;

        let mut args_code = Vec::with_capacity(args.len());
        for arg in args {
            args_code.push(self.expr_codegen(arg)?.into());
        }

        self.builder
            .build_call(func, &args_code, "tmpcall")
            .try_as_basic_value()
            .left()
            .ok_or_else(|| "Invalid call?".to_string())
    }

    // if then optional else
    fn cond_codegen(
        &mut self,
        cond_expr: &Expression,
        then_expr: &[&Expression],
        else_expr: &Option<Vec<&Expression>>, // todo: can this be a slice?
    ) -> StmtCgResult<'ctx> {
        // Get the current function for insertion
        let parent = self
            .builder
            .get_insert_block()
            .and_then(|x| x.get_parent())
            .ok_or("Parent function not found when building conditional")?;

        // CodeGen expression. Will be optimized to a 0 or 1 if comparing
        // constants. Otherwise, the value will be IR to evaluate. Result will
        // be a float 0 or 1.
        let cond_val = self.expr_codegen(cond_expr)?.into_int_value(); // XXX

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

        // CodeGen the else block if we have one
        if let Some(ee) = else_expr {
            for expr in ee {
                self.expr_codegen(expr)?;
            }

            // Make sure the alternative returns to the end block after execution
            self.builder.build_unconditional_branch(end_block);

            // Point the builder at the end of the empty end block
            self.builder.position_at_end(end_block);
        }

        Ok(())
    }

    // for start; cond; step { body }
    // start == let var_name = x
    fn for_codegen(
        &mut self,
        var_name: &str,
        start: &Node,
        cond: &Node,
        step: &Node,
        body: &[Node],
    ) -> StmtCgResult<'ctx> {
        let parent = self
            .builder
            .get_insert_block()
            .and_then(|x| x.get_parent())
            .ok_or("Parent function not found when building loop")?;

        // Create entry alloca, codegen start expr, and store result
        let start_alloca = self.create_entry_block_alloca((var_name, Type::U64), &parent); // XXX
        let start_code = self.expr_codegen(start.as_expr()?)?;
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
            self.expr_codegen(expr.as_expr()?)?;
        }

        // Codegen step value and end cond
        let step_code = self.expr_codegen(step.as_expr()?)?;
        let cond_code = self.expr_codegen(cond.as_expr()?)?.into_int_value(); // XXX

        // Load the current induction variable from the stack, increment it by
        // step, and store it again. Body could have mutated it.
        let cur = self.builder.build_load(start_alloca, var_name);
        let next =
            self.builder
                .build_int_add(cur.into_int_value(), step_code.into_int_value(), "incvar"); // XXX
        self.builder.build_store(start_alloca, next);

        let cond_bool = self.builder.build_int_compare(
            IntPredicate::NE,
            cond_code,
            self.context.i64_type().const_zero(), // XXX
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

        Ok(())
    }

    fn unop_codegen(&mut self, op: Symbol, rhs: &Expression) -> ExprCgResult<'ctx> {
        use Symbol::*;

        let rhs = self.expr_codegen(rhs)?;
        match op {
            Minus => Ok(self
                .builder
                .build_int_neg(rhs.into_int_value(), "neg") // XXX
                .as_basic_value_enum()),
            x => Err(format!("Unknown unary operator: {}", x)),
        }
    }

    fn let_codegen(
        &mut self,
        name: &str,
        ty: Type,
        init: &Option<&Expression>,
    ) -> StmtCgResult<'ctx> {
        let parent = self
            .builder
            .get_insert_block()
            .and_then(|x| x.get_parent())
            .ok_or("Parent function not found when building let expression")?;

        // match ty {
        //     Type::U64 => todo!(),
        //     Type::I64 => todo!("i64 let"),
        //     Type::F64 => todo!("f64 let"),
        // };

        let init_code = match init {
            Some(init) => self.expr_codegen(init)?,
            None => self.context.i64_type().const_zero().as_basic_value_enum(),
        };

        let init_alloca = self.create_entry_block_alloca((name, ty), &parent);
        self.builder.build_store(init_alloca, init_code);

        self.local_vars.insert(name.to_owned(), init_alloca);

        Ok(())
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
            glob!("tests/inputs/*.input", |path| {
                let input = fs::read_to_string(path).unwrap();
                let tokens = Lexer::new(&input).collect::<Result<Vec<_>, _>>().unwrap();
                let parser = Parser::new(&tokens);
                let ast = parser.parse().unwrap();

                let context = Context::create();
                let builder = context.create_builder();
                let module = context.create_module("main_mod");
                let fpm = PassManager::create(&module);
                let mut codegen = CodeGen::new(&context, &builder, &module, &fpm);

                assert_yaml_snapshot!(code_to_string(codegen.walk(&ast)));
            });
        });
    }
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
/*
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
    let cond_code = self.expr_codegen(cond)?.into_int_value(); // XXX

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
 */
