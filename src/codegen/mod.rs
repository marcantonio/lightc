use either::Either;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::passes::PassManager;
use inkwell::types::BasicMetadataTypeEnum;
use inkwell::values::{BasicValue, BasicValueEnum, FunctionValue, PhiValue, PointerValue};
use inkwell::IntPredicate;
use std::collections::HashMap;

use crate::ast::conversion::AsExpr;
use crate::ast::{Ast, Expression, Literal};
use crate::ast::{AstVisitor, Prototype, Visitable};
use crate::ast::{Node, Statement};
use crate::token::{Symbol, Type};
use lightc::*;

mod ops;

type StmtResult<'ctx> = Result<(), String>;
type ExprResult<'ctx> = Result<BasicValueEnum<'ctx>, String>;

// Generate IR for the AST. If types mismatch at this stage, it's a compiler
// bug, not user error.

pub(crate) struct Codegen<'a, 'ctx> {
    context: &'ctx Context,
    builder: &'a Builder<'ctx>,
    module: &'a Module<'ctx>,
    fpm: &'a PassManager<FunctionValue<'ctx>>,
    local_vars: HashMap<String, PointerValue<'ctx>>,
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
    pub(crate) fn new(
        context: &'ctx Context,
        builder: &'a Builder<'ctx>,
        module: &'a Module<'ctx>,
        fpm: &'a PassManager<FunctionValue<'ctx>>,
        opt_level: usize,
        skip_verify: bool,
    ) -> Self {
        let values = HashMap::new();

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
            local_vars: values,
            main: None,
            opt_level,
            skip_verify,
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
            int8_types!() => builder.build_alloca(self.context.i8_type(), name),
            int16_types!() => builder.build_alloca(self.context.i16_type(), name),
            int32_types!() => builder.build_alloca(self.context.i32_type(), name),
            int64_types!() => builder.build_alloca(self.context.i64_type(), name),
            Type::Float => builder.build_alloca(self.context.f32_type(), name),
            Type::Double => builder.build_alloca(self.context.f64_type(), name),
            Type::Void => unreachable!(
                "NONCANBE: void type for stack variable in create_entry_block_alloca()"
            ),
            Type::Bool => builder.build_alloca(self.context.bool_type(), name),
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
                start_name,
                *start_antn,
                start_expr,
                cond_expr,
                step_expr,
                body,
            ),
            Let { name, antn, init } => self.codegen_let(name, *antn, &init.as_expr()?),
            Fn { proto, body } => self.codegen_func(proto, body),
        }
    }

    fn codegen_proto(&self, proto: &Prototype) -> Result<FunctionValue<'ctx>, String> {
        let args_type = proto
            .args
            .iter()
            .map(|x| {
                let (_, ty) = x;
                match ty {
                    int8_types!() => BasicMetadataTypeEnum::IntType(self.context.i8_type()),
                    int16_types!() => BasicMetadataTypeEnum::IntType(self.context.i16_type()),
                    int32_types!() => BasicMetadataTypeEnum::IntType(self.context.i32_type()),
                    int64_types!() => BasicMetadataTypeEnum::IntType(self.context.i64_type()),
                    Type::Float => BasicMetadataTypeEnum::FloatType(self.context.f32_type()),
                    Type::Double => BasicMetadataTypeEnum::FloatType(self.context.f64_type()),
                    Type::Bool => BasicMetadataTypeEnum::IntType(self.context.bool_type()),
                    Type::Void => {
                        unreachable!("NONCANBE: void type for prototype args in codegen_proto()")
                    }
                }
            })
            .collect::<Vec<BasicMetadataTypeEnum>>();

        // Generate function based on return type
        let func_type = match proto.ret_ty {
            Some(int8_types!()) => self.context.i8_type().fn_type(&args_type, false),
            Some(int16_types!()) => self.context.i16_type().fn_type(&args_type, false),
            Some(int32_types!()) => self.context.i32_type().fn_type(&args_type, false),
            Some(int64_types!()) => self.context.i64_type().fn_type(&args_type, false),
            Some(Type::Float) => self.context.f32_type().fn_type(&args_type, false),
            Some(Type::Double) => self.context.f64_type().fn_type(&args_type, false),
            Some(_) | None => self.context.void_type().fn_type(&args_type, false),
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

    fn codegen_func(&mut self, proto: &Prototype, body: &Option<Vec<Node>>) -> StmtResult<'ctx> {
        let function = self.codegen_proto(proto)?;
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

        // Generate and add all expressions in the body. Save the last to one to
        // use with the ret instruction. Note: We can't use codegen_node() here
        // because we need the return value.
        let mut last_node_val = None;
        for node in body {
            last_node_val = match node {
                Node::Stmt(s) => {
                    self.codegen_stmt(s)?;
                    None
                }
                Node::Expr(e) => self.codegen_expr(e)?,
            }
        }

        // Build the return function based on the prototype's return value and the last statement
        match (proto.ret_ty, last_node_val) {
            (Some(numeric_types!()), Some(v)) => self.builder.build_return(Some(&v)),
            (Some(rt), None) if rt != Type::Void => {
                return Err(format!(
                    "Function should return {} but last statement is void",
                    rt
                ))
            }
            _ => self.builder.build_return(None),
        };

        // Identify main
        let func_name = function.get_name().to_str().unwrap();
        if func_name == "main" {
            self.main = Some(function);
        }

        // Some times it's useful to skip verification just so we can see the
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
    // start == let var_name = x
    fn codegen_for(
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
        let start_code = self.codegen_expr(start_expr)?.value()?;
        self.builder.build_store(start_alloca, start_code);

        // Create a block for the loop, a branch to it, and move the insertion
        // to it
        let loop_bb = self.context.append_basic_block(parent, "for.loop");
        self.builder.build_unconditional_branch(loop_bb);
        self.builder.position_at_end(loop_bb);

        // Save the variable value if we are shadowing and insert alloca into
        // local map
        let old_var = self.local_vars.remove(start_name);
        self.local_vars.insert(start_name.to_owned(), start_alloca);

        // Generate all body expressions
        for node in body {
            self.codegen_node(node)?;
        }

        // Codegen step value and end cond
        let step_code = self.codegen_expr(step_expr)?;
        let cond_code = self.codegen_expr(cond_expr)?.value()?.into_int_value();

        // Load the current induction variable from the stack, increment it by
        // step, and store it again. Body could have mutated it.
        let cur = self.builder.build_load(start_alloca, start_name);
        match start_expr.ty() {
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
            _ => unreachable!("NONCANBE: void type for step in codegen_for()"),
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
        self.local_vars.remove(start_name);
        if let Some(v) = old_var {
            self.local_vars.insert(start_name.to_owned(), v);
        }

        Ok(())
    }

    fn codegen_let(
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

        // Match combinations of init presence and type. When init is None,
        // initialize with 0.
        let init_code = match (ty, init) {
            (_, Some(init)) => {
                if init.ty() == Some(ty) {
                    self.codegen_expr(init)?
                } else {
                    unreachable!("NONCANBE: void type for init expr in codegen_let()");
                }
            }
            (int8_types!(), None) => {
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
            (Type::Void, None) => {
                unreachable!("NONCANBE: void type for init annotation in codegen_let()")
            }
        };

        let init_alloca = self.create_entry_block_alloca(name, ty, &parent);
        self.builder.build_store(init_alloca, init_code.value()?);
        self.local_vars.insert(name.to_owned(), init_alloca);

        Ok(())
    }

    fn codegen_expr(&mut self, expr: &Expression) -> Result<Option<BasicValueEnum<'ctx>>, String> {
        use Expression::*;

        match expr {
            Lit { value, .. } => Some(self.codegen_lit(value)),
            Ident { name, .. } => Some(self.codegen_ident(name)),
            BinOp { sym, lhs, rhs, .. } => {
                Some(self.codegen_binop(*sym, lhs.as_expr()?, rhs.as_expr()?))
            }
            UnOp { sym, rhs, .. } => Some(self.codegen_unop(*sym, rhs.as_expr()?)),
            Call { name, args, .. } => self.codegen_call(name, &args.as_expr()?).transpose(),
            Cond {
                cond_expr,
                then_block,
                else_block,
                ty,
            } => Some(self.codegen_cond(cond_expr, then_block, else_block, ty.unwrap())),
        }
        .transpose()
    }

    fn codegen_lit(&self, value: &Literal) -> ExprResult<'ctx> {
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
            UInt8(v) => self
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
        })
    }

    fn codegen_ident(&self, name: &str) -> ExprResult<'ctx> {
        // Get the variable pointer and load from the stack
        match self.local_vars.get(name) {
            Some(var) => Ok(self.builder.build_load(*var, name)),
            None => Err(format!("Unknown variable: {}", name)),
        }
    }

    fn codegen_call(
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

    fn codegen_binop(
        &mut self,
        op: Symbol,
        lhs: &Expression,
        rhs: &Expression,
    ) -> ExprResult<'ctx> {
        use Symbol::*;

        // If assignment, make sure lvalue is a variable and store rhs there
        if op == Assign {
            let l_var = match lhs {
                Expression::Ident { name, .. } => name,
                _ => return Err("Expected LHS to be a variable for assignment".to_string()),
            };

            let r_val = self.codegen_expr(rhs)?.value()?;
            let l_var = self
                .local_vars
                .get(l_var)
                .ok_or(format!("Unknown variable in assignment: {}", l_var))?
                .to_owned();

            self.builder.build_store(l_var, r_val);

            return Ok(r_val);
        }

        let lhs_val = self.codegen_expr(lhs)?.value()?;
        let lhs_ty = lhs.ty().unwrap_or_else(|| {
            unreachable!("NONCANBE: missing type for lhs expr in codegen_binop()")
        });
        let rhs_val = self.codegen_expr(rhs)?.value()?;
        let rhs_ty = rhs.ty().unwrap_or_else(|| {
            unreachable!("NONCANBE: missing type for rhs expr in codegen_binop()")
        });

        // Generate the proper instruction for each op
        match op {
            Add => self.add((lhs_val, lhs_ty), (rhs_val, rhs_ty)),
            Sub => self.sub((lhs_val, lhs_ty), (rhs_val, rhs_ty)),
            Mul => self.mul((lhs_val, lhs_ty), (rhs_val, rhs_ty)),
            Div => self.div((lhs_val, lhs_ty), (rhs_val, rhs_ty)),
            And => self.and((lhs_val, lhs_ty), (rhs_val, rhs_ty)),
            Or => self.or((lhs_val, lhs_ty), (rhs_val, rhs_ty)),
            op @ (Gt | Lt | Eq) => self.cmp(op, (lhs_val, lhs_ty), (rhs_val, rhs_ty)),
            x => Err(format!("Unknown binary operator: {}", x)),
        }
    }

    fn codegen_unop(&mut self, op: Symbol, rhs: &Expression) -> ExprResult<'ctx> {
        use Symbol::*;

        let rhs_val = self.codegen_expr(rhs)?.value()?;
        let rhs_ty = rhs.ty().unwrap();
        match op {
            Sub => self.neg((rhs_val, rhs_ty)),
            x => Err(format!("Unknown unary operator: {}", x)),
        }
    }

    // if then optional else
    fn codegen_cond(
        &mut self,
        cond_expr: &Expression,
        then_block: &[Node],
        else_block: &Option<Vec<Node>>,
        ty: Type,
    ) -> ExprResult<'ctx> {
        // Should never be used. Useful for an unused phi branch.
        let undef_val = self.context.i32_type().get_undef().as_basic_value_enum();

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
        let mut last_then_val = undef_val;
        for node in then_block {
            if let Some(val) = self.codegen_node(node)? {
                last_then_val = val;
            }
        }

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
            // Codegen the then block. Save the last value for phi.
            let mut last_else_val = undef_val;
            for node in else_block {
                if let Some(val) = self.codegen_node(node)? {
                    last_else_val = val;
                }
            }

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
            let phi = self.build_phi_for_type(ty, "if.else.phi");
            phi.add_incoming(&[(&last_then_val, then_bb), (&last_else_val, else_bb)]);
            val = phi.as_basic_value();
        } else {
            let phi = self.build_phi_for_type(ty, "if.phi");
            phi.add_incoming(&[(&last_then_val, then_bb), (&undef_val, entry_bb)]);
            val = phi.as_basic_value();
        }
        Ok(val)
    }

    fn build_phi_for_type(&self, ty: Type, name: &str) -> PhiValue<'ctx> {
        let name = name.to_owned();
        match ty {
            int8_types!() => self
                .builder
                .build_phi(self.context.i8_type(), &(name + ".int8")),
            int16_types!() => self
                .builder
                .build_phi(self.context.i16_type(), &(name + ".int16")),
            int32_types!() => self
                .builder
                .build_phi(self.context.i32_type(), &(name + ".int32")),
            int64_types!() => self
                .builder
                .build_phi(self.context.i64_type(), &(name + ".int64")),
            Type::Float => self
                .builder
                .build_phi(self.context.f32_type(), &(name + ".float")),
            Type::Double => self
                .builder
                .build_phi(self.context.f64_type(), &(name + ".double")),
            Type::Bool => self
                .builder
                .build_phi(self.context.bool_type(), &(name + ".bool")),
            Type::Void => self
                .builder
                .build_phi(self.context.i32_type(), &(name + ".void")),
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

#[cfg(test)]
mod test {
    use inkwell::passes::PassManager;
    use inkwell::values::FunctionValue;
    use inkwell::{context::Context, values::AnyValue};
    use std::io::BufRead;

    use super::*;
    use crate::lexer::Lexer;
    use crate::parser::Parser;
    use crate::type_checker::TypeChecker;

    // This is how we "deserialize" FunctionValue to work with insta
    fn code_to_string(code: Result<FunctionValue, String>) -> String {
        match code {
            Ok(code) => code.print_to_string().to_string(),
            Err(err) => err,
        }
    }

    #[test]
    fn test_codegen() {
        insta::with_settings!({ snapshot_path => "tests/snapshots", prepend_module_to_snapshot => false }, {
            insta::glob!("tests/inputs/*.input", |path| {
                let file = std::fs::File::open(path).expect("Error reading input file");
                let reader = std::io::BufReader::new(file);

                // Each line of the input files is meant to be a separate test
                // case.
                let ir = reader
                    .lines()
                    .map(|line| {
                        let line = line.expect("Error reading input line");
                        let tokens = Lexer::new(&line).scan().unwrap_or_else(|err| panic!("test failure in `{:?}`: {}", path, err));
                        let mut ast = Parser::new(&tokens).parse().unwrap_or_else(|err| panic!("test failure in `{:?}`: {}", path, err));
                        TypeChecker::new().walk(&mut ast).unwrap_or_else(|err| panic!("test failure in `{:?}`: {}", path, err));
                        let context = Context::create();
                        let builder = context.create_builder();
                        let module = context.create_module("main_mod");
                        let fpm = PassManager::create(&module);
                        let mut codegen = Codegen::new(&context, &builder, &module, &fpm, 1, false);
                        code_to_string(codegen.walk(&ast))
                    })
                    .collect::<Vec<_>>();
                insta::assert_yaml_snapshot!(ir);
            });
        });
    }
}
