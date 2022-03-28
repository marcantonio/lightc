use either::Either;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::passes::PassManager;
use inkwell::types::{BasicMetadataTypeEnum, BasicTypeEnum};
use inkwell::values::{BasicValue, BasicValueEnum, FunctionValue, PointerValue};
use inkwell::IntPredicate;
use std::collections::HashMap;

use crate::ast::conversion::AsExpr;
use crate::ast::{Ast, Expression, Literal};
use crate::ast::{AstVisitor, Prototype, Visitable};
use crate::ast::{Node, Statement};
use crate::token::{Symbol, Type};

type StmtResult<'ctx> = Result<(), String>;
type ExprResult<'ctx> = Result<BasicValueEnum<'ctx>, String>;

macro_rules! extract_type {
    ($ctx:expr, $var:expr) => {{
        let (_, ty) = $var;
        match ty {
            Type::U64 | Type::I64 => BasicMetadataTypeEnum::IntType($ctx.i64_type()),
            Type::F64 => BasicMetadataTypeEnum::FloatType($ctx.f64_type()),
            _ => todo!("extract"),
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

impl<'a, 'ctx> AstVisitor for CodeGen<'a, 'ctx> {
    type Result = Result<(), String>;

    fn visit_stmt(&mut self, s: &Statement) -> Self::Result {
        self.stmt_codegen(s)
    }

    fn visit_expr(&mut self, e: &Expression) -> Self::Result {
        self.expr_codegen(e)?;
        Ok(())
    }
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
    pub(crate) fn walk(&mut self, ast: &Ast<Node>) -> Result<FunctionValue, String> {
        for node in ast.nodes() {
            node.accept(self)?;
        }
        self.main.ok_or_else(|| "main() not found".to_string())
    }

    // Helper to create an alloca in the entry block for local variables
    fn create_entry_block_alloca(
        &self,
        name: &str,
        ty: Type,
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
            Type::U64 | Type::I64 => builder.build_alloca(self.context.i64_type(), name),
            Type::F64 => builder.build_alloca(self.context.f64_type(), name),
            _ => todo!("alloc"),
        }
    }

    // Helper function for when we don't know if we have a statement or an
    // expression
    fn node_codegen(&mut self, node: &Node) -> StmtResult<'ctx> {
        match node {
            Node::Stmt(s) => self.stmt_codegen(s),
            Node::Expr(e) => {
                self.expr_codegen(e)?;
                Ok(())
            }
        }
    }

    fn stmt_codegen(&mut self, stmt: &Statement) -> StmtResult<'ctx> {
        use Statement::*;
        match stmt {
            Cond {
                cond_expr,
                then_block,
                else_block,
            } => self.cond_codegen(cond_expr, then_block, &else_block.as_expr()?),
            For {
                start_name,
                start_antn,
                start_expr,
                cond_expr,
                step_expr,
                body,
            } => self.for_codegen(
                start_name,
                *start_antn,
                start_expr,
                cond_expr,
                step_expr,
                body,
            ),
            Let { name, antn, init } => self.let_codegen(name, *antn, &init.as_expr()?),
            Fn { proto, body } => self.func_codegen(proto, body),
        }
    }

    fn proto_codegen(&self, proto: &Prototype) -> Result<FunctionValue<'ctx>, String> {
        let args_type = proto
            .args
            .iter()
            .map(|x| extract_type!(self.context, x))
            .collect::<Vec<BasicMetadataTypeEnum>>();

        // Generate function based on return type
        let func_type = match proto.ret_type {
            Some(Type::F64) => self.context.f64_type().fn_type(&args_type, false),
            Some(Type::U64 | Type::I64) => self.context.i64_type().fn_type(&args_type, false),
            Some(_) => todo!("proto"),
            None => self.context.void_type().fn_type(&args_type, false),
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

    fn func_codegen(&mut self, proto: &Prototype, body: &Option<Vec<Node>>) -> StmtResult<'ctx> {
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
            let alloca = self.create_entry_block_alloca(x, *y, &function);
            self.builder.build_store(alloca, arg);
            self.local_vars.insert(proto.args[i].0.to_owned(), alloca);
        }

        //todo: no redefining functions

        // Generate and add all expressions in the body. Save the last to one to
        // use with the ret instruction. Note: We can't use codegen_node() here
        // because we need the return value.
        let mut last_node_val = None;
        for node in body {
            last_node_val = match node {
                Node::Stmt(s) => {
                    self.stmt_codegen(s)?;
                    None
                }
                Node::Expr(e) => self.expr_codegen(e)?,
            }
        }

        // Build the return function based on the prototype's return value and the last statement
        match (proto.ret_type, last_node_val) {
            (Some(Type::F64 | Type::I64 | Type::U64), Some(v)) => {
                self.builder.build_return(Some(&v))
            }
            (Some(rt), None) => {
                return Err(format!(
                    "Function should return {} but last statement is void",
                    rt
                ))
            }
            _ => self.builder.build_return(None),
        };

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

    fn expr_codegen(&mut self, expr: &Expression) -> Result<Option<BasicValueEnum<'ctx>>, String> {
        use Expression::*;
        match expr {
            Lit { value, .. } => Some(self.lit_codegen(value)),
            Ident { name, .. } => Some(self.ident_codegen(name)),
            BinOp { sym, lhs, rhs, .. } => {
                Some(self.binop_codegen(*sym, lhs.as_expr()?, rhs.as_expr()?))
            }
            UnOp { sym, rhs, .. } => Some(self.unop_codegen(*sym, rhs.as_expr()?)),
            Call { name, args, .. } => self.call_codegen(name, &args.as_expr()?).transpose(),
        }
        .transpose()
    }

    fn lit_codegen(&self, value: &Literal) -> ExprResult<'ctx> {
        Ok(match value {
            Literal::I64(v) => self
                .context
                .i64_type()
                .const_int(*v as u64, true)
                .as_basic_value_enum(),
            Literal::U64(v) => self
                .context
                .i64_type()
                .const_int(*v, false)
                .as_basic_value_enum(),
            Literal::F64(v) => self
                .context
                .f64_type()
                .const_float(*v)
                .as_basic_value_enum(),
        })
    }

    fn ident_codegen(&self, name: &str) -> ExprResult<'ctx> {
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
    ) -> ExprResult<'ctx> {
        use super::token::Symbol::*;

        // If assignment, make sure lvalue is a variable and store rhs there
        if op == Assign {
            let l_var = match lhs {
                Expression::Ident { name, .. } => name,
                _ => return Err("Expected LHS to be a variable for assignment".to_string()),
            };

            let r_val = self.expr_codegen(rhs)?.ret_val()?;
            let l_var = self
                .local_vars
                .get(l_var)
                .ok_or(format!("Unknown variable in assignment: {}", l_var))?
                .to_owned();

            self.builder.build_store(l_var, r_val);

            return Ok(r_val);
        }

        let lhs = self.expr_codegen(lhs)?.ret_val()?; // Valuable? Inner?
        let rhs = self.expr_codegen(rhs)?.ret_val()?;

        // Generate the proper instruction for each op
        match op {
            Add => self.add(lhs, rhs),
            Div => Ok(self
                .builder
                .build_int_unsigned_div(lhs.into_int_value(), rhs.into_int_value(), "tmpdiv")
                .as_basic_value_enum()),
            Mul => self.mul(lhs, rhs),
            Sub => self.sub(lhs, rhs),
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
                    _ => {
                        return Err(
                            "noncanbe: Something went really wrong in binop_codegen()".to_string()
                        )
                    }
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

    fn call_codegen(
        &mut self,
        name: &str,
        args: &[&Expression],
    ) -> Result<Option<BasicValueEnum<'ctx>>, String> {
        // Look up the function. Error if it's not been defined.
        let func = self
            .module
            .get_function(name)
            .ok_or(format!("Unknown function call: {}", name))?;

        // Codegen the call args
        let mut args_code = Vec::with_capacity(args.len());
        for arg in args {
            args_code.push((self.expr_codegen(arg)?.ret_val()?).into());
        }

        // Build the call instruction
        let call_val = self
            .builder
            .build_call(func, &args_code, &("call_".to_owned() + name));

        // If func has a non-void return type, it will produce a call_val that
        // is converted into a BasicValueEnum. Otherwise it becomes an
        // InstructionValue, which we ignore.
        Ok(match call_val.try_as_basic_value() {
            Either::Left(v) => Some(v),
            Either::Right(_) => None,
        })
    }

    // if then optional else
    fn cond_codegen(
        &mut self,
        cond_expr: &Expression,
        then_block: &[Node],
        else_block: &Option<Vec<&Expression>>,
    ) -> StmtResult<'ctx> {
        // Get the current function for insertion
        let parent = self
            .builder
            .get_insert_block()
            .and_then(|x| x.get_parent())
            .ok_or_else(|| "Parent function not found when building conditional".to_string())?;

        // CodeGen expression. Will be optimized to a 0 or 1 if comparing
        // constants. Otherwise, the value will be IR to evaluate. Result will
        // be a float 0 or 1.
        let cond_val = self.expr_codegen(cond_expr)?.ret_val()?.into_int_value(); // XXX

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
        let then_bb = self.context.append_basic_block(parent, "if.then");
        let end_bb = self.context.append_basic_block(parent, "if.end");
        let mut else_bb = end_bb;
        if else_block.is_some() {
            else_bb = self.context.append_basic_block(parent, "if.else");
            else_bb
                .move_before(end_bb)
                .map_err(|_| String::from("LLVM error"))?;
        }

        // Emits the entry conditional branch instructions
        self.builder
            .build_conditional_branch(cond_bool, then_bb, else_bb);

        // Point the builder at the end of the empty then block
        self.builder.position_at_end(then_bb);

        // CodeGen the then block
        for node in then_block {
            self.node_codegen(node)?;
        }

        // Make sure the consequent returns to the end block after execution
        self.builder.build_unconditional_branch(end_bb);

        // Point the builder at the end of the empty else block
        self.builder.position_at_end(else_bb);

        // CodeGen the else block if we have one
        if let Some(ee) = else_block {
            for expr in ee {
                self.expr_codegen(expr)?;
            }

            // Make sure the alternative returns to the end block after execution
            self.builder.build_unconditional_branch(end_bb);

            // Point the builder at the end of the empty end block
            self.builder.position_at_end(end_bb);
        }

        Ok(())
    }

    // for start; cond; step { body }
    // start == let var_name = x
    fn for_codegen(
        &mut self,
        start_name: &str,
        start_antn: Type,
        start_expr: &Expression,
        cond_expr: &Expression,
        step_expr: &Expression,
        body: &[Node],
    ) -> StmtResult<'ctx> {
        let parent = self
            .builder
            .get_insert_block()
            .and_then(|x| x.get_parent())
            .ok_or_else(|| "Parent function not found when building loop".to_string())?;

        // Create entry alloca, codegen start expr, and store result
        let start_alloca = self.create_entry_block_alloca(start_name, start_antn, &parent);
        let start_code = self.expr_codegen(start_expr)?.ret_val()?;
        self.builder.build_store(start_alloca, start_code);

        // Create a block for the loop, a branch to it, and move the insertion
        // to it
        let loop_bb = self.context.append_basic_block(parent, "loop");
        self.builder.build_unconditional_branch(loop_bb);
        self.builder.position_at_end(loop_bb);

        // Save the variable value if we are shadowing and insert alloca into
        // local map
        let old_var = self.local_vars.remove(start_name);
        self.local_vars.insert(start_name.to_owned(), start_alloca);

        // Generate all body expressions
        for node in body {
            self.node_codegen(node)?;
        }

        // Codegen step value and end cond
        let step_code = self.expr_codegen(step_expr)?;
        let cond_code = self.expr_codegen(cond_expr)?.ret_val()?.into_int_value(); // XXX

        // Load the current induction variable from the stack, increment it by
        // step, and store it again. Body could have mutated it.
        let cur = self.builder.build_load(start_alloca, start_name);
        let next = self.builder.build_int_add(
            cur.into_int_value(),
            step_code.ret_val()?.into_int_value(),
            "incvar",
        ); // XXX
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
        self.local_vars.remove(start_name);
        if let Some(v) = old_var {
            self.local_vars.insert(start_name.to_owned(), v);
        }

        Ok(())
    }

    fn unop_codegen(&mut self, op: Symbol, rhs: &Expression) -> ExprResult<'ctx> {
        use Symbol::*;

        let rhs = self.expr_codegen(rhs)?.ret_val()?;
        match op {
            Sub => Ok(match rhs.get_type() {
                BasicTypeEnum::FloatType(_) => self
                    .builder
                    .build_float_neg(rhs.into_float_value(), "neg")
                    .as_basic_value_enum(),
                BasicTypeEnum::IntType(_) => self
                    .builder
                    .build_int_neg(rhs.into_int_value(), "neg")
                    .as_basic_value_enum(),
                _ => todo!(),
            }),
            x => Err(format!("Unknown unary operator: {}", x)),
        }
    }

    fn let_codegen(
        &mut self,
        name: &str,
        ty: Type,
        init: &Option<&Expression>,
    ) -> StmtResult<'ctx> {
        let parent = self
            .builder
            .get_insert_block()
            .and_then(|x| x.get_parent())
            .ok_or_else(|| "Parent function not found when building let statement".to_string())?;

        let init_code = match (ty, init) {
            (_, Some(i)) => {
                if i.ty() == Some(ty) {
                    self.expr_codegen(i)?
                } else {
                    return Err(format!(
                        "Types don't match in let statement. Annotated with {} but value is {}",
                        ty,
                        i.ty().unwrap_or(Type::U64) // XXX
                    ));
                }
            }
            (Type::U64, None) => Some(self.context.i64_type().const_zero().as_basic_value_enum()),
            (Type::I64, None) => Some(self.context.i64_type().const_zero().as_basic_value_enum()),
            (Type::F64, None) => Some(self.context.f64_type().const_zero().as_basic_value_enum()),
            _ => todo!("let"),
        };

        let init_alloca = self.create_entry_block_alloca(name, ty, &parent);
        self.builder.build_store(init_alloca, init_code.ret_val()?);
        self.local_vars.insert(name.to_owned(), init_alloca);

        Ok(())
    }

    fn add(&self, lhs: BasicValueEnum<'ctx>, rhs: BasicValueEnum<'ctx>) -> ExprResult<'ctx> {
        match lhs.get_type() {
            BasicTypeEnum::IntType(_) => Ok(self
                .builder
                .build_int_add(lhs.into_int_value(), rhs.into_int_value(), "intadd")
                .as_basic_value_enum()),
            BasicTypeEnum::FloatType(_) => Ok(self
                .builder
                .build_float_add(lhs.into_float_value(), rhs.into_float_value(), "floatadd")
                .as_basic_value_enum()),
            _ => Err("Unsupported types in add operation".to_string()),
        }
    }

    fn sub(&self, lhs: BasicValueEnum<'ctx>, rhs: BasicValueEnum<'ctx>) -> ExprResult<'ctx> {
        match lhs.get_type() {
            BasicTypeEnum::IntType(_) => Ok(self
                .builder
                .build_int_sub(lhs.into_int_value(), rhs.into_int_value(), "intsub")
                .as_basic_value_enum()),
            BasicTypeEnum::FloatType(_) => Ok(self
                .builder
                .build_float_sub(lhs.into_float_value(), rhs.into_float_value(), "floatsub")
                .as_basic_value_enum()),
            _ => Err("Unsupported types in subtract operation".to_string()),
        }
    }

    fn mul(&self, lhs: BasicValueEnum<'ctx>, rhs: BasicValueEnum<'ctx>) -> ExprResult<'ctx> {
        match lhs.get_type() {
            BasicTypeEnum::IntType(_) => Ok(self
                .builder
                .build_int_mul(lhs.into_int_value(), rhs.into_int_value(), "intmul")
                .as_basic_value_enum()),
            BasicTypeEnum::FloatType(_) => Ok(self
                .builder
                .build_float_mul(lhs.into_float_value(), rhs.into_float_value(), "floatmul")
                .as_basic_value_enum()),
            _ => Err("Unsupported types in multiply operation".to_string()),
        }
    }
}

// trait DoMath<T> {
//     type Result;
//     fn sub(&self, lhs: T, rhs: T) -> Self::Result;
// }

// impl<'a, 'ctx> DoMath<FloatValue<'ctx>> for CodeGen<'a, 'ctx> {
//     type Result = BasicValueEnum<'ctx>;

//     fn sub(&self, lhs: FloatValue<'ctx>, rhs: FloatValue<'ctx>) -> Self::Result {
//         self.builder
//             .build_float_sub(lhs, rhs, "floatsub")
//             .as_basic_value_enum()
//     }
// }

// impl<'a, 'ctx> DoMath<IntValue<'ctx>> for CodeGen<'a, 'ctx> {
//     type Result = BasicValueEnum<'ctx>;

//     fn sub(&self, lhs: IntValue<'ctx>, rhs: IntValue<'ctx>) -> Self::Result {
//         self.builder
//             .build_int_sub(lhs, rhs, "floatsub")
//             .as_basic_value_enum()
//     }
// }

#[cfg(test)]
mod test {
    use inkwell::passes::PassManager;
    use inkwell::values::FunctionValue;
    use inkwell::{context::Context, values::AnyValue};
    use insta::{assert_yaml_snapshot, glob, with_settings};
    use std::fs::File;
    use std::io::BufRead;
    use std::io::BufReader;

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
                let file = File::open(path).expect("Error reading input file");
                let reader = BufReader::new(file);

                // Each line of the input files is meant to be a separate test
                // case. Treat each as its own AST. Including `ast_string` in the
                // output makes it more readable.
                let ir = reader
                    .lines()
                    .map(|line| {
                        let line = line.expect("Error reading input line");
                        let tokens = Lexer::new(&line).collect::<Result<Vec<_>, _>>().unwrap();
                        let ast = Parser::new(&tokens).parse().unwrap_or_else(|_| panic!("file: {:?}", path)); // XXX
                        let context = Context::create();
                        let builder = context.create_builder();
                        let module = context.create_module("main_mod");
                        let fpm = PassManager::create(&module);
                        let mut codegen = CodeGen::new(&context, &builder, &module, &fpm);
                        code_to_string(codegen.walk(&ast))
                    })
                    .collect::<Vec<_>>();
                assert_yaml_snapshot!(ir);
            });
        });
    }
}

// Like unwrap() but with a fixed error message. Necessary to allow call_expr to
// return an Option for void calls.
trait AsRetVal<T> {
    type Result;

    fn ret_val(self) -> Result<T, Self::Result>;
}

impl<T> AsRetVal<T> for Option<T> {
    type Result = String;

    fn ret_val(self) -> Result<T, Self::Result> {
        match self {
            Some(v) => Ok(v),
            None => Err("Expected value, found void".to_string()),
        }
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
    let cond_code = self.expr_codegen(cond)?.into_int_value();

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
