use either::Either;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::passes::PassManager;
use inkwell::types::{AnyType, AnyTypeEnum, BasicMetadataTypeEnum, BasicType};
use inkwell::values::{BasicValue, BasicValueEnum, FunctionValue, PointerValue};
use inkwell::IntPredicate;

use ast::convert::AsExpr;
use ast::{Ast, AstVisitor, Expression, Literal, Node, Prototype, Statement, Visitable};
use common::symbol_table::SymbolTable;
use common::{Symbol, Type};

#[macro_use]
extern crate common;

#[macro_use]
mod macros;
mod ops;
#[cfg(test)]
mod tests;

type StmtResult<'ctx> = Result<(), String>;
type ExprResult<'ctx> = Result<BasicValueEnum<'ctx>, String>;

// Generate IR for the AST. If types mismatch at this stage, it's a compiler
// bug, not user error.

pub struct Codegen<'a, 'ctx> {
    context: &'ctx Context,
    builder: &'a Builder<'ctx>,
    module: &'a Module<'ctx>,
    fpm: &'a PassManager<FunctionValue<'ctx>>,
    symbol_table: SymbolTable<PointerValue<'ctx>>,
    main: Option<FunctionValue<'ctx>>,
    opt_level: usize,
    skip_verify: bool,
}

impl<'a, 'ctx> AstVisitor for Codegen<'a, 'ctx> {
    type Result = Result<(), String>;

    fn visit_stmt(&mut self, s: &Statement) -> Self::Result {
        self.codegen_stmt(s)
    }

    fn visit_expr(&mut self, e: &Expression) -> Self::Result {
        self.codegen_expr(e)?;
        Ok(())
    }
}

impl<'a, 'ctx> Codegen<'a, 'ctx> {
    pub fn new(
        context: &'ctx Context,
        builder: &'a Builder<'ctx>,
        module: &'a Module<'ctx>,
        fpm: &'a PassManager<FunctionValue<'ctx>>,
        opt_level: usize,
        skip_verify: bool,
    ) -> Self {
        if opt_level > 0 {
            fpm.add_instruction_combining_pass();
            fpm.add_reassociate_pass();
            fpm.add_gvn_pass();
            fpm.add_cfg_simplification_pass();
            fpm.add_basic_alias_analysis_pass();
            fpm.add_promote_memory_to_register_pass();
            fpm.add_instruction_combining_pass();
            fpm.add_reassociate_pass();
            fpm.initialize();
        }

        Codegen {
            context,
            builder,
            module,
            fpm,
            symbol_table: SymbolTable::new(),
            main: None,
            opt_level,
            skip_verify,
        }
    }

    // Iterate over all nodes and codegen. Optionally return a string (for
    // testing).
    pub fn walk(&mut self, ast: &Ast<Node>) -> Result<(), String> {
        for node in ast.nodes() {
            node.accept(self)?;
        }
        if self.main.is_none() {
            Err("main() not found".to_string())
        } else {
            Ok(())
        }
    }

    // Helper function for when we don't know if we have a statement or an
    // expression
    fn codegen_node(&mut self, node: &Node) -> Result<Option<BasicValueEnum<'ctx>>, String> {
        match node {
            Node::Stmt(s) => {
                self.codegen_stmt(s)?;
                Ok(None)
            }
            Node::Expr(e) => self.codegen_expr(e),
        }
    }

    fn codegen_stmt(&mut self, stmt: &Statement) -> StmtResult<'ctx> {
        use Statement::*;

        match stmt {
            For {
                start_name,
                start_antn,
                start_expr,
                cond_expr,
                step_expr,
                body,
            } => self.codegen_for(
                start_name, start_antn, start_expr, cond_expr, step_expr, body,
            ),
            Let { name, antn, init } => self.codegen_let(name, antn, init.as_deref()),
            Fn { proto, body } => self.codegen_func(proto, &body.as_deref()),
        }
    }

    fn codegen_proto(&self, proto: &Prototype) -> Result<FunctionValue<'ctx>, String> {
        let args_type = proto
            .args()
            .iter()
            .map(|x| {
                let (_, ty) = x;
                match self.get_llvm_ty(ty.clone()) {
                    AnyTypeEnum::FloatType(ty) => BasicMetadataTypeEnum::FloatType(ty),
                    AnyTypeEnum::IntType(ty) => BasicMetadataTypeEnum::IntType(ty),
                    ty => unreachable!(
                        "fatal: unsupported argument type `{}` in prototype `{}()`",
                        ty.print_to_string(),
                        proto.name(),
                    ),
                }
            })
            .collect::<Vec<BasicMetadataTypeEnum>>();

        // Generate function based on return type
        let func_type = match self.get_llvm_ty(proto.ret_ty().cloned().unwrap_or_default()) {
            AnyTypeEnum::FloatType(ty) => ty.fn_type(&args_type, false),
            AnyTypeEnum::IntType(ty) => ty.fn_type(&args_type, false),
            AnyTypeEnum::VoidType(ty) => ty.fn_type(&args_type, false),
            ty => unreachable!(
                "fatal: unsupported return type `{}` in prototype `{}()`",
                ty.print_to_string(),
                proto.name(),
            ),
        };

        // Add function to current module's symbold table. Defaults to external
        // linkage with None.
        let func = self.module.add_function(proto.name(), func_type, None);

        // Name all args
        func.get_param_iter().enumerate().for_each(|(i, arg)| {
            arg.set_name(&proto.args()[i].0);
        });

        Ok(func)
    }

    fn codegen_func<T: AsExpr<Expression>>(
        &mut self,
        proto: &Prototype,
        body: &Option<&T>,
    ) -> StmtResult<'ctx> {
        let function = self.codegen_proto(proto)?;
        // If body is None assume call is an extern
        let body = match body {
            Some(body) => body.as_expr(),
            None => return Ok(()),
        };

        // Create new block for function
        let bb = self.context.append_basic_block(function, "entry");

        // Make sure the builder will insert new instructions at the end
        self.builder.position_at_end(bb);

        // Allocate space for the function's arguments on the stack
        for (i, arg) in function.get_param_iter().enumerate() {
            let (x, y) = &proto.args()[i];
            let alloca = self.create_entry_block_alloca(x, y, &function);
            self.builder.build_store(alloca, arg);
            self.symbol_table.insert(&proto.args()[i].0, alloca)?;
        }

        let body_val = self.codegen_expr(body)?;

        // Build the return function based on the prototype's return value and the last statement
        match (proto.ret_ty(), body_val) {
            (Some(numeric_types!() | Type::Bool), Some(v)) => self.builder.build_return(Some(&v)),
            (Some(rt), None) if rt != &Type::Void => {
                return Err(format!(
                    "Function should return `{}` but last statement is void",
                    rt
                ))
            }
            _ => self.builder.build_return(None),
        };

        // Remove arguments from the table
        for (i, _) in function.get_param_iter().enumerate() {
            self.symbol_table.remove(&proto.args()[i].0);
        }

        // Identify main
        let func_name = function.get_name().to_str().unwrap();
        if func_name == "main" {
            self.main = Some(function);
        }

        // Some times it's useful to skip verification just so we can see the IR
        if !self.skip_verify {
            // Make sure we didn't miss anything
            // TODO: Should this allow llvm to print or use a verbose flag, or are
            // the errors not useful?
            if function.verify(true) {
                if self.opt_level > 0 {
                    // Only run optimizations on verified functions
                    self.fpm.run_on(&function);
                }
            } else {
                // Useful for JIT, if we support that later
                // unsafe {
                //     function.delete();
                // }
                return Err(format!("Error compiling: {}", func_name));
            }
        }
        Ok(())
    }

    // for start; cond; step { body }
    fn codegen_for<T: AsExpr<Expression>>(
        &mut self,
        start_name: &str,
        start_antn: &Type,
        start_expr: &T,
        cond_expr: &T,
        step_expr: &T,
        body: &T,
    ) -> StmtResult<'ctx> {
        let parent = self
            .builder
            .get_insert_block()
            .and_then(|x| x.get_parent())
            .ok_or_else(|| "Parent function not found when building loop".to_string())?;

        // Create entry alloca, codegen start expr, and store result
        let start_alloca = self.create_entry_block_alloca(start_name, start_antn, &parent);
        let start_code = self.codegen_expr(start_expr)?.value()?;
        self.builder.build_store(start_alloca, start_code);

        // Create a block for the loop, a branch to it, and move the insertion
        // to it
        let loop_bb = self.context.append_basic_block(parent, "for.loop");
        self.builder.build_unconditional_branch(loop_bb);
        self.builder.position_at_end(loop_bb);

        // Save the variable value if we are shadowing and insert alloca into
        // local map
        let old_var = self.symbol_table.remove(start_name);
        self.symbol_table.insert(start_name, start_alloca)?;

        // Generate all body expressions
        self.codegen_expr(body)?;

        // Codegen step value and end cond
        let step_code = self.codegen_expr(step_expr)?;
        let cond_code = self.codegen_expr(cond_expr)?.value()?.into_int_value();

        // Load the current induction variable from the stack, increment it by
        // step, and store it again. Body could have mutated it.
        let cur = self.builder.build_load(start_alloca, start_name);
        match start_expr.as_expr().ty() {
            Some(int_types!()) => {
                let next = self.builder.build_int_add(
                    cur.into_int_value(),
                    step_code.value()?.into_int_value(),
                    "for.int.step",
                );
                self.builder.build_store(start_alloca, next);
            }
            Some(float_types!()) => {
                let next = self.builder.build_float_add(
                    cur.into_float_value(),
                    step_code.value()?.into_float_value(),
                    "for.float.step",
                );
                self.builder.build_store(start_alloca, next);
            }
            _ => unreachable!("NONCANBE: void type for step in codegen_for()"), // XXX: not just void
        };

        let cond_bool = self.builder.build_int_compare(
            IntPredicate::NE,
            cond_code,
            self.context.bool_type().const_zero(),
            "for.cond",
        );

        // Append a block for after the loop and insert the loop conditional at
        // the end
        let after_bb = self.context.append_basic_block(parent, "for.after");
        self.builder
            .build_conditional_branch(cond_bool, loop_bb, after_bb);
        self.builder.position_at_end(after_bb);

        // Reset shadowed variable
        self.symbol_table.remove(start_name);
        if let Some(v) = old_var {
            self.symbol_table.insert(start_name, v)?;
        }

        Ok(())
    }

    fn codegen_let<T: AsExpr<Expression>>(
        &mut self,
        name: &str,
        ty: &Type,
        init: Option<&T>,
    ) -> StmtResult<'ctx> {
        let parent = self
            .builder
            .get_insert_block()
            .and_then(|x| x.get_parent())
            .ok_or_else(|| "Parent function not found when building let statement".to_string())?;

        // Match combinations of init presence and type. When init is None,
        // initialize with 0.
        let init_code = match (ty, init) {
            (_, Some(init)) => {
                if init.as_expr().ty() == Some(ty) {
                    self.codegen_expr(init)?
                } else {
                    unreachable!("fatal: void type for init expr in codegen_let()");
                }
            }
            (int8_types!() | Type::Char, None) => {
                Some(self.context.i8_type().const_zero().as_basic_value_enum())
            }
            (int16_types!(), None) => {
                Some(self.context.i16_type().const_zero().as_basic_value_enum())
            }
            (int32_types!(), None) => {
                Some(self.context.i32_type().const_zero().as_basic_value_enum())
            }
            (int64_types!(), None) => {
                Some(self.context.i64_type().const_zero().as_basic_value_enum())
            }
            (Type::Float, None) => Some(self.context.f32_type().const_zero().as_basic_value_enum()),
            (Type::Double, None) => {
                Some(self.context.f64_type().const_zero().as_basic_value_enum())
            }
            (Type::Bool, None) => Some(self.context.bool_type().const_zero().as_basic_value_enum()),
            (Type::Void | Type::Array(..), None) => {
                unreachable!("NONCANBE: void type for init annotation in codegen_let()")
            }
        };

        let init_alloca = self.create_entry_block_alloca(name, ty, &parent);
        self.builder.build_store(init_alloca, init_code.value()?);
        self.symbol_table.insert(name, init_alloca)?;

        Ok(())
    }

    fn codegen_expr<T: AsExpr<Expression>>(
        &mut self,
        expr: &T,
    ) -> Result<Option<BasicValueEnum<'ctx>>, String> {
        use Expression::*;

        match expr.as_expr() {
            Lit { value, .. } => Some(self.codegen_lit(value)),
            Ident { name, .. } => Some(self.codegen_ident(name)),
            BinOp { sym, lhs, rhs, .. } => Some(self.codegen_binop(*sym, lhs, rhs)),
            UnOp { sym, rhs, .. } => Some(self.codegen_unop(*sym, rhs)),
            Call { name, args, .. } => self.codegen_call(name, args).transpose(),
            Cond {
                cond_expr,
                then_block,
                else_block,
                ty,
            } => Some(self.codegen_cond(
                cond_expr,
                then_block,
                else_block.as_ref(),
                ty.as_ref().unwrap(),
            )),
            Block { list, .. } => self.codegen_block(list).transpose(),
            Index { .. } => todo!(),
        }
        .transpose()
    }

    fn codegen_block(&mut self, list: &[Node]) -> Result<Option<BasicValueEnum<'ctx>>, String> {
        // Drop scope
        self.symbol_table.down_scope();

        let mut node_val = None;
        for node in list {
            node_val = self.codegen_node(node)?;
        }

        // Pop up 1 level. Drops old scope.
        self.symbol_table.up_scope()?;

        Ok(node_val)
    }

    fn codegen_lit(&mut self, value: &Literal) -> ExprResult<'ctx> {
        use Literal::*;

        Ok(match value {
            Int8(v) => self
                .context
                .i8_type()
                .const_int(*v as u64, true)
                .as_basic_value_enum(),
            Int16(v) => self
                .context
                .i16_type()
                .const_int(*v as u64, true)
                .as_basic_value_enum(),
            Int32(v) => self
                .context
                .i32_type()
                .const_int(*v as u64, true)
                .as_basic_value_enum(),
            Int64(v) => self
                .context
                .i64_type()
                .const_int(*v as u64, true)
                .as_basic_value_enum(),
            UInt8(v) | Char(v) => self
                .context
                .i8_type()
                .const_int(*v as u64, false)
                .as_basic_value_enum(),
            UInt16(v) => self
                .context
                .i16_type()
                .const_int(*v as u64, false)
                .as_basic_value_enum(),
            UInt32(v) => self
                .context
                .i32_type()
                .const_int(*v as u64, false)
                .as_basic_value_enum(),
            UInt64(v) => self
                .context
                .i64_type()
                .const_int(*v, false)
                .as_basic_value_enum(),
            Float(v) => self
                .context
                .f32_type()
                .const_float(*v as f64)
                .as_basic_value_enum(),
            Double(v) => self
                .context
                .f64_type()
                .const_float(*v)
                .as_basic_value_enum(),
            Bool(v) => self
                .context
                .bool_type()
                .const_int(*v as u64, true)
                .as_basic_value_enum(),
            Array { elements, inner_ty } => {
                let len = elements.len();
                let mut vals = Vec::with_capacity(len);
                for el in elements {
                    vals.push(self.codegen_node(el)?.unwrap());
                }
                match self.get_llvm_ty(inner_ty.as_ref().cloned().unwrap()) {
                    AnyTypeEnum::FloatType(ty) => {
                        let vals = vals
                            .iter()
                            .map(|v| v.into_float_value())
                            .collect::<Vec<_>>();
                        ty.const_array(&vals).as_basic_value_enum()
                    }
                    AnyTypeEnum::IntType(ty) => {
                        let vals = vals.iter().map(|v| v.into_int_value()).collect::<Vec<_>>();
                        ty.const_array(&vals).as_basic_value_enum()
                    }
                    _ => todo!(),
                }
            }
        })
    }

    fn codegen_ident(&self, name: &str) -> ExprResult<'ctx> {
        // Get the variable pointer and load from the stack
        let var = self
            .symbol_table
            .get(name)
            .unwrap_or_else(|| unreachable!("Fatal: codegen failed to resolve `{}`", name));
        Ok(self.builder.build_load(var, name))
    }

    fn codegen_call<T: AsExpr<Expression>>(
        &mut self,
        name: &str,
        args: &[T],
    ) -> Result<Option<BasicValueEnum<'ctx>>, String> {
        // Look up the function. Error if it's not been defined.
        let func = self
            .module
            .get_function(name)
            .ok_or(format!("Unknown function call: {}", name))?;

        // Codegen the call args
        let mut args_code = Vec::with_capacity(args.len());
        for arg in args {
            args_code.push((self.codegen_expr(arg)?.value()?).into());
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

    fn codegen_binop<T: AsExpr<Expression>>(
        &mut self,
        op: Symbol,
        lhs: &T,
        rhs: &T,
    ) -> ExprResult<'ctx> {
        use Symbol::*;

        let lhs = lhs.as_expr();
        let rhs = rhs.as_expr();

        let lhs_val = self.codegen_expr(lhs)?.value()?;
        let lhs_ty = lhs
            .ty()
            .unwrap_or_else(|| unreachable!("fatal: missing type for lhs expr in codegen_binop()"));
        let rhs_val = self.codegen_expr(rhs)?.value()?;
        let rhs_ty = rhs
            .ty()
            .unwrap_or_else(|| unreachable!("fatal: missing type for rhs expr in codegen_binop()"));

        // Generate the proper instruction for each op
        match op {
            Add => self.add((lhs_val, lhs_ty), (rhs_val, rhs_ty)),
            Sub => self.sub((lhs_val, lhs_ty), (rhs_val, rhs_ty)),
            Mul => self.mul((lhs_val, lhs_ty), (rhs_val, rhs_ty)),
            Div => self.div((lhs_val, lhs_ty), (rhs_val, rhs_ty)),
            And => self.and((lhs_val, lhs_ty), (rhs_val, rhs_ty)),
            Or => self.or((lhs_val, lhs_ty), (rhs_val, rhs_ty)),
            Assign => self.assign(lhs, rhs_val),
            op @ (Gt | Lt | Eq) => self.cmp(op, (lhs_val, lhs_ty), (rhs_val, rhs_ty)),
            x => Err(format!("Unknown binary operator: {}", x)),
        }
    }

    fn codegen_unop<T: AsExpr<Expression>>(&mut self, op: Symbol, rhs: &T) -> ExprResult<'ctx> {
        use Symbol::*;

        let rhs_val = self.codegen_expr(rhs)?.value()?;
        let rhs_ty = rhs.as_expr().ty().unwrap();
        match op {
            Sub => self.neg((rhs_val, rhs_ty)),
            x => Err(format!("Unknown unary operator: {}", x)),
        }
    }

    // if then optional else
    fn codegen_cond<T: AsExpr<Expression>>(
        &mut self,
        cond_expr: &T,
        then_block: &T,
        else_block: Option<&T>,
        ty: &Type,
    ) -> ExprResult<'ctx> {
        // Should never be used. Useful for an unused phi branch. Note: undef
        // value must be in sync with phi type.
        let undef_val = make_undef_value!(self.context, ty);

        // Get the current function for insertion
        let parent = self
            .builder
            .get_insert_block()
            .and_then(|x| x.get_parent())
            .ok_or_else(|| "Parent function not found when building conditional".to_string())?;

        // Get the starting basic block. This is only used later if there is no
        // else block, but we need to capture it now before we start appending
        // new blocks.
        let entry_bb = parent.get_last_basic_block().unwrap();

        // Codegen expression. Will be optimized to a 0 or 1 if comparing
        // constants. Otherwise, the value will be IR to evaluate. Result will
        // be a 0 or 1. Then compare cond_val to 0. Result will be a 1 bit
        // "bool".
        let cond_val = self.codegen_expr(cond_expr)?.value()?.into_int_value();
        let cond_bool = self.builder.build_int_compare(
            IntPredicate::NE,
            cond_val,
            self.context.bool_type().const_zero(),
            "if.cond.int",
        );

        // Create blocks for branches and after. The else block is just a
        // pointer to end if there's no else expression.
        let mut then_bb = self.context.append_basic_block(parent, "if.then");
        let end_bb = self.context.append_basic_block(parent, "if.end");
        let mut else_bb = end_bb;
        if else_block.is_some() {
            else_bb = self.context.append_basic_block(parent, "if.else");
        }

        // Emits the entry conditional branch instructions
        self.builder
            .build_conditional_branch(cond_bool, then_bb, else_bb);

        // Point the builder at the end of the empty then block
        self.builder.position_at_end(then_bb);

        // Codegen the then block. Save the last value for phi.
        let then_val = match self.codegen_expr(then_block)? {
            Some(v) => v,
            None => undef_val,
        };

        // Make sure the consequent returns to the end block after its
        // execution. Don't forget to reset `then_bb` in case codegen moved it.
        self.builder.build_unconditional_branch(end_bb);
        then_bb = self
            .builder
            .get_insert_block()
            .ok_or("Can't reset `then` block")?;

        // Point the builder at the end of the empty else/end block
        self.builder.position_at_end(else_bb);

        let val;
        // Codegen the else block if we have one
        if let Some(else_block) = else_block {
            // Codegen the else block. Save the last value for phi.
            let else_val = match self.codegen_expr(else_block)? {
                Some(v) => v,
                None => undef_val,
            };

            // Make sure the alternative returns to the end block after its
            // execution. Don't forget to reset `then_bb` in case codegen moved it.
            self.builder.build_unconditional_branch(end_bb);
            else_bb = self
                .builder
                .get_insert_block()
                .ok_or("Can't reset `else` block")?;

            // Point the builder at the end of the empty end block
            self.builder.position_at_end(end_bb);

            // Create the phi node and insert code/value pairs
            let phi = make_phi_for_type!(self.builder, self.context, ty, "if.else.phi");
            phi.add_incoming(&[(&then_val, then_bb), (&else_val, else_bb)]);
            val = phi.as_basic_value();
        } else {
            let phi = make_phi_for_type!(self.builder, self.context, ty, "if.phi");
            phi.add_incoming(&[(&then_val, then_bb), (&undef_val, entry_bb)]);
            val = phi.as_basic_value();
        }
        Ok(val)
    }

    // Helper to create an alloca in the entry block for local variables
    fn create_entry_block_alloca(
        &self,
        name: &str,
        ty: &Type,
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
            int8_types!() | Type::Char => builder.build_alloca(self.context.i8_type(), name),
            int16_types!() => builder.build_alloca(self.context.i16_type(), name),
            int32_types!() => builder.build_alloca(self.context.i32_type(), name),
            int64_types!() => builder.build_alloca(self.context.i64_type(), name),
            Type::Float => builder.build_alloca(self.context.f32_type(), name),
            Type::Double => builder.build_alloca(self.context.f64_type(), name),
            Type::Void => unreachable!(
                "NONCANBE: void type for stack variable in create_entry_block_alloca()"
            ),
            Type::Bool => builder.build_alloca(self.context.bool_type(), name),
            Type::Array(ty, ..) => {
                let ty = match self.get_llvm_ty(ty.as_ref().clone()) {
                    AnyTypeEnum::FloatType(ty) => ty.as_basic_type_enum(),
                    AnyTypeEnum::IntType(ty) => ty.as_basic_type_enum(),
                    _ => todo!(),
                };
                builder.build_alloca(ty.array_type(3), name)
            }
        }
    }

    fn get_llvm_ty(&self, ty: Type) -> AnyTypeEnum<'ctx> {
        match ty {
            int8_types!() | Type::Char => self.context.i8_type().as_any_type_enum(),
            int16_types!() => self.context.i16_type().as_any_type_enum(),
            int32_types!() => self.context.i32_type().as_any_type_enum(),
            int64_types!() => self.context.i64_type().as_any_type_enum(),
            Type::Float => self.context.f32_type().as_any_type_enum(),
            Type::Double => self.context.f64_type().as_any_type_enum(),
            Type::Bool => self.context.bool_type().as_any_type_enum(),
            Type::Void => self.context.void_type().as_any_type_enum(),
            Type::Array(ty, size) => match self.get_llvm_ty(*ty) {
                AnyTypeEnum::ArrayType(ty) => ty.array_type(size).as_any_type_enum(),
                AnyTypeEnum::FloatType(ty) => ty.array_type(size).as_any_type_enum(),
                AnyTypeEnum::IntType(ty) => ty.array_type(size).as_any_type_enum(),
                _ => todo!(),
            },
        }
    }
}

// Like unwrap() but with a fixed error message. Necessary to allow call_expr to
// return an Option for void calls.
trait Valuable<T> {
    type Result;

    fn value(self) -> Result<T, Self::Result>;
}

impl<T> Valuable<T> for Option<T> {
    type Result = String;

    fn value(self) -> Result<T, Self::Result> {
        match self {
            Some(v) => Ok(v),
            None => Err("Expected value, found void".to_string()),
        }
    }
}
