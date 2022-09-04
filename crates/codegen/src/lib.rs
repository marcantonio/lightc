use std::path::PathBuf;
use std::process;

use either::Either;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::passes::PassManager;
use inkwell::targets::{FileType, InitializationConfig, Target, TargetMachine};
use inkwell::types::{AnyType, AnyTypeEnum, BasicMetadataTypeEnum, BasicType};
use inkwell::values::{BasicValue, BasicValueEnum, FunctionValue, PointerValue};
use inkwell::{IntPredicate, OptimizationLevel};

use ast::{Ast, AstVisitor, Expression, Literal, Node, Prototype, Statement, Visitable};
use codegen_symbol::CodegenSymbol;
use common::{CliArgs, Operator, Type};
use symbol_table::{Symbol, SymbolTable};

#[macro_use]
extern crate common;

mod codegen_symbol;
#[macro_use]
mod macros;
mod jit_externs;
mod ops;
#[cfg(test)]
mod tests;

type StmtResult<'ctx> = Result<(), String>;
type ExprResult<'ctx> = Result<BasicValueEnum<'ctx>, String>;

// Generate IR for the AST. If types mismatch at this stage, it's a compiler
// bug, not user error.

pub struct Codegen<'ctx> {
    context: &'ctx Context,
    builder: Builder<'ctx>,
    module: Module<'ctx>,
    fpm: PassManager<FunctionValue<'ctx>>,
    symbol_table: SymbolTable<CodegenSymbol<'ctx>>,
    main: Option<FunctionValue<'ctx>>,
    opt_level: usize,
    no_verify: bool,
    require_main: bool,
}

impl<'ctx> AstVisitor for Codegen<'ctx> {
    type Result = Result<(), String>;

    fn visit_stmt(&mut self, s: Statement) -> Self::Result {
        self.codegen_stmt(s)
    }

    fn visit_expr(&mut self, e: Expression) -> Self::Result {
        self.codegen_expr(e)?;
        Ok(())
    }
}

impl<'ctx> Codegen<'ctx> {
    pub fn run_pass(
        hir: Ast<Node>, module_name: &str, symbol_table: SymbolTable<Symbol>, build_dir: PathBuf,
        args: &CliArgs, is_test: bool,
    ) -> Result<CodegenResult, String> {
        let context = Context::create();
        let builder = context.create_builder();
        let module = context.create_module(module_name);

        let fpm = PassManager::create(&module);
        if args.opt_level > 0 {
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

        let symbol_table: SymbolTable<CodegenSymbol<'ctx>> = Codegen::convert_table(symbol_table)?;

        let mut codegen = Codegen {
            context: &context,
            builder,
            module,
            fpm,
            symbol_table,
            main: None,
            opt_level: args.opt_level,
            no_verify: args.no_verify,
            require_main: !args.compile_only,
        };

        codegen.walk(hir)?;

        // This flag is just for the test suite
        if is_test {
            return Ok(CodegenResult::Ir(codegen.module.print_to_string().to_string()));
        }

        if args.show_ir {
            println!("IR:");
            println!("{}", codegen.module.print_to_string().to_string());
        }

        if args.run_jit {
            Codegen::run_jit(&codegen.module);
            process::exit(0);
        }

        // File name for module binary
        let mut module_file = build_dir;
        module_file.push(&module_name);
        let module_file = module_file.as_path().with_extension("o");

        // Write the object file to the build directory
        let target_machine = Codegen::build_target_machine(&codegen.module);
        target_machine
            .write_to_file(&codegen.module, FileType::Object, &module_file)
            .expect("Error writing object file");

        Ok(CodegenResult::FilePath(module_file))
    }

    // Optimizes for host CPU
    // TODO: Make more generic
    fn build_target_machine(module: &Module) -> TargetMachine {
        Target::initialize_x86(&InitializationConfig::default());
        let triple = TargetMachine::get_default_triple();
        let target = Target::from_triple(&triple).expect("Target error");
        let target_machine = target
            .create_target_machine(
                &triple,
                &TargetMachine::get_host_cpu_name().to_string(),
                &TargetMachine::get_host_cpu_features().to_string(),
                OptimizationLevel::Default,
                inkwell::targets::RelocMode::Default,
                inkwell::targets::CodeModel::Default,
            )
            .expect("Target machine error");

        module.set_data_layout(&target_machine.get_target_data().get_data_layout());
        module.set_triple(&triple);
        target_machine
    }

    fn run_jit(module: &Module) {
        jit_externs::load();

        let ee = module.create_jit_execution_engine(OptimizationLevel::None).unwrap();

        let f = unsafe { ee.get_function::<unsafe extern "C" fn() -> i64>("main") };
        match f {
            Ok(f) => unsafe {
                let ret = f.call();
                eprintln!("main() return value: {:?}", ret);
            },
            Err(e) => {
                eprintln!("JIT execution error: {}", e);
            },
        };
    }

    // Iterate over all nodes and codegen
    pub fn walk(&mut self, ast: Ast<Node>) -> Result<(), String> {
        for node in ast.into_nodes() {
            node.accept(self)?;
        }
        if self.require_main && self.main.is_none() {
            Err("Function main() required in executable and not found".to_string())
        } else {
            Ok(())
        }
    }

    // Helper function for when we don't know if we have a statement or an
    // expression
    fn codegen_node(&mut self, node: Node) -> Result<Option<BasicValueEnum<'ctx>>, String> {
        match node {
            Node::Stmt(s) => {
                self.codegen_stmt(s)?;
                Ok(None)
            },
            Node::Expr(e) => self.codegen_expr(e),
        }
    }

    fn codegen_stmt(&mut self, stmt: Statement) -> StmtResult<'ctx> {
        use Statement::*;

        match stmt {
            For { start_name, start_antn, start_expr, cond_expr, step_expr, body } => {
                self.codegen_for(start_name, start_antn, start_expr, *cond_expr, *step_expr, *body)
            },
            Let(l) => self.codegen_let(l),
            Fn { proto, body } => self.codegen_func(*proto, body),
            Struct(s) => self.codegen_struct(s),
        }
    }

    // for start; cond; step { body }
    fn codegen_for(
        &mut self, start_name: String, start_antn: Type, start_expr: Option<Box<Node>>, cond_expr: Node,
        step_expr: Node, body: Node,
    ) -> StmtResult<'ctx> {
        let parent = self
            .builder
            .get_insert_block()
            .and_then(|x| x.get_parent())
            .ok_or_else(|| "Parent function not found when building loop".to_string())?;

        // Create entry alloca, codegen start expr, and store result
        let start_alloca = self.create_entry_block_alloca(&start_name, &start_antn, &parent);
        let start_code = self.codegen_var_init(&start_antn, start_expr)?;
        self.builder.build_store(start_alloca, start_code);

        // Create interstitial scope to protect the induction variable
        self.symbol_table.enter_scope();

        // Save new symbol with alloca
        let start_sym = CodegenSymbol::from((start_name.as_str(), &start_antn, start_alloca));
        self.symbol_table.insert(start_sym);

        // Create all the blocks
        let cond_bb = self.context.append_basic_block(parent, "for.cond");
        let body_bb = self.context.append_basic_block(parent, "for.body");
        let step_bb = self.context.append_basic_block(parent, "for.step");
        let post_bb = self.context.append_basic_block(parent, "for.post");

        // Jump from entry to cond_bb
        self.builder.build_unconditional_branch(cond_bb);

        // Generate the conditional and branch to either the body or the end
        self.builder.position_at_end(cond_bb);
        let cond_code = self.codegen_node(cond_expr)?.value()?.into_int_value();
        self.builder.build_conditional_branch(cond_code, body_bb, post_bb);

        // Generate all body expressions
        self.builder.position_at_end(body_bb);
        self.codegen_node(body)?;
        self.builder.build_unconditional_branch(step_bb);

        // Generate step value, load the current induction variable from the stack, increment it by
        // step, and store it again. Body could have mutated it.
        self.builder.position_at_end(step_bb);
        let step_code = self.codegen_node(step_expr)?;
        let cur = self.builder.build_load(start_alloca, &start_name);
        match start_antn {
            int_types!() => {
                let next = self.builder.build_int_add(
                    cur.into_int_value(),
                    step_code.value()?.into_int_value(),
                    "for.int.step",
                );
                self.builder.build_store(start_alloca, next);
            },
            float_types!() => {
                let next = self.builder.build_float_add(
                    cur.into_float_value(),
                    step_code.value()?.into_float_value(),
                    "for.float.step",
                );
                self.builder.build_store(start_alloca, next);
            },
            ty => unreachable!("invalid type: `{}` found in for step in `codegen_for()`", ty),
        };

        // Loop around to the beginning
        self.builder.build_unconditional_branch(cond_bb);

        // Set insertion to after the loop
        self.builder.position_at_end(post_bb);

        self.symbol_table.leave_scope();

        Ok(())
    }

    fn codegen_let(&mut self, l: ast::Let) -> StmtResult<'ctx> {
        let parent = self
            .builder
            .get_insert_block()
            .and_then(|x| x.get_parent())
            .ok_or_else(|| "Parent function not found when building let statement".to_string())?;

        let init_code = self.codegen_var_init(&l.antn, l.init)?;

        let init_alloca = self.create_entry_block_alloca(&l.name, &l.antn, &parent);
        self.builder.build_store(init_alloca, init_code);

        let sym = CodegenSymbol::from((l.name.as_str(), &l.antn, init_alloca));
        self.symbol_table.insert(sym);

        Ok(())
    }

    fn codegen_func(&mut self, proto: Prototype, body: Option<Box<Node>>) -> StmtResult<'ctx> {
        // Creates interstitial scope for the arguments in the function definition
        self.symbol_table.enter_scope();

        let function = self.codegen_proto(&proto)?;

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
        for (i, arg) in function.get_param_iter().enumerate() {
            let (name, ty) = &proto.args()[i];
            let alloca = self.create_entry_block_alloca(name, ty, &function);
            self.builder.build_store(alloca, arg);
            self.symbol_table.insert(CodegenSymbol::from((name.as_str(), ty, alloca)));
        }

        let body_val = self.codegen_node(*body)?;

        // Build the return function based on the prototype's return value and the last statement
        match (proto.ret_ty(), body_val) {
            (Some(numeric_types!() | Type::Bool), Some(v)) => self.builder.build_return(Some(&v)),
            (Some(rt), None) if rt != &Type::Void => {
                return Err(format!("Function should return `{}` but last statement is void", rt))
            },
            _ => self.builder.build_return(None),
        };

        self.symbol_table.leave_scope();

        // Identify main
        let func_name = function.get_name().to_str().unwrap();
        if func_name == "main" {
            self.main = Some(function);
        }

        // Some times it's useful to skip verification just so we can see the IR
        if !self.no_verify {
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

    fn codegen_proto(&self, proto: &Prototype) -> Result<FunctionValue<'ctx>, String> {
        let args_type = proto
            .args()
            .iter()
            .map(|x| {
                let (_, ty) = x;
                match self.get_llvm_ty(ty.clone()) {
                    AnyTypeEnum::FloatType(ty) => BasicMetadataTypeEnum::FloatType(ty),
                    AnyTypeEnum::IntType(ty) => BasicMetadataTypeEnum::IntType(ty),
                    AnyTypeEnum::ArrayType(ty) => BasicMetadataTypeEnum::ArrayType(ty),
                    ty => unreachable!(
                        "unsupported argument type `{}` in prototype `{}()`",
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
                "unsupported return type `{}` in prototype `{}()`",
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

    // XXX: not useful yet
    fn codegen_struct(&mut self, s: ast::Struct) -> StmtResult<'ctx> {
        // Drop scope
        //self.scope_table.down_scope();

        for node in s.fields {
            self.codegen_node(node)?;
        }

        for node in s.methods {
            self.codegen_node(node)?;
        }

        // Pop up 1 level. Drops old scope.
        //self.scope_table.up_scope()?;

        Ok(())
    }

    fn codegen_expr(&mut self, expr: Expression) -> Result<Option<BasicValueEnum<'ctx>>, String> {
        use Expression::*;

        match expr {
            Lit { value, .. } => Some(self.codegen_lit(value)),
            Ident { name, .. } => Some(self.codegen_ident(&name)),
            BinOp { op, lhs, rhs, .. } => Some(self.codegen_binop(op, *lhs, *rhs)),
            UnOp { op, rhs, .. } => Some(self.codegen_unop(op, *rhs)),
            Call { name, args, .. } => self.codegen_call(&name, args).transpose(),
            Cond { cond_expr, then_block, else_block, ty } => {
                Some(self.codegen_cond(*cond_expr, *then_block, else_block, ty.as_ref().unwrap()))
            },
            Block { list, .. } => self.codegen_block(list).transpose(),
            Index { binding, idx, .. } => Some(self.codegen_index(*binding, *idx)),
        }
        .transpose()
    }

    fn codegen_lit(&mut self, value: Literal) -> ExprResult<'ctx> {
        use Literal::*;

        Ok(match value {
            Int8(v) => self.context.i8_type().const_int(v as u64, true).as_basic_value_enum(),
            Int16(v) => self.context.i16_type().const_int(v as u64, true).as_basic_value_enum(),
            Int32(v) => self.context.i32_type().const_int(v as u64, true).as_basic_value_enum(),
            Int64(v) => self.context.i64_type().const_int(v as u64, true).as_basic_value_enum(),
            UInt8(v) | Char(v) => self.context.i8_type().const_int(v as u64, false).as_basic_value_enum(),
            UInt16(v) => self.context.i16_type().const_int(v as u64, false).as_basic_value_enum(),
            UInt32(v) => self.context.i32_type().const_int(v as u64, false).as_basic_value_enum(),
            UInt64(v) => self.context.i64_type().const_int(v, false).as_basic_value_enum(),
            Float(v) => self.context.f32_type().const_float(v as f64).as_basic_value_enum(),
            Double(v) => self.context.f64_type().const_float(v).as_basic_value_enum(),
            Bool(v) => self.context.bool_type().const_int(v as u64, true).as_basic_value_enum(),
            Array { elements, inner_ty } => {
                let len = elements.len();
                let mut vals = Vec::with_capacity(len);
                for el in elements {
                    vals.push(self.codegen_node(el)?.unwrap());
                }
                match self.get_llvm_ty(inner_ty.as_ref().cloned().unwrap()) {
                    AnyTypeEnum::FloatType(ty) => {
                        let vals = vals.iter().map(|v| v.into_float_value()).collect::<Vec<_>>();
                        ty.const_array(&vals).as_basic_value_enum()
                    },
                    AnyTypeEnum::IntType(ty) => {
                        let vals = vals.iter().map(|v| v.into_int_value()).collect::<Vec<_>>();
                        ty.const_array(&vals).as_basic_value_enum()
                    },
                    _ => todo!(),
                }
            },
        })
    }

    fn codegen_ident(&self, name: &str) -> ExprResult<'ctx> {
        // Get the variable pointer and load from the stack
        let ptr = self
            .symbol_table
            .get(name)
            .unwrap_or_else(|| panic!("codegen failed to resolve `{}`", name))
            .pointer()
            .expect("missing pointer on symbol");
        Ok(self.builder.build_load(ptr, name))
    }

    fn codegen_binop(&mut self, op: Operator, lhs: Node, rhs: Node) -> ExprResult<'ctx> {
        use Operator::*;

        let lhs_ty =
            lhs.ty().unwrap_or_else(|| unreachable!("missing type for lhs expr in `codegen_binop()`"));
        let lhs_val = self.codegen_node(lhs.clone())?.value()?;
        let rhs_ty =
            rhs.ty().unwrap_or_else(|| unreachable!("missing type for rhs expr in `codegen_binop()`"));
        let rhs_val = self.codegen_node(rhs)?.value()?;

        // Generate the proper instruction for each op
        match op {
            Add => self.add((lhs_val, lhs_ty), (rhs_val, rhs_ty)),
            Sub => self.sub((lhs_val, lhs_ty), (rhs_val, rhs_ty)),
            Mul => self.mul((lhs_val, lhs_ty), (rhs_val, rhs_ty)),
            Div => self.div((lhs_val, lhs_ty), (rhs_val, rhs_ty)),
            And | BitAnd => self.and((lhs_val, lhs_ty), (rhs_val, rhs_ty)),
            BitXor => self.xor((lhs_val, lhs_ty), (rhs_val, rhs_ty)),
            Or | BitOr => self.or((lhs_val, lhs_ty), (rhs_val, rhs_ty)),
            Assign => self.assign(lhs, rhs_val),
            op @ (Gt | GtEq | Lt | LtEq | Eq | NotEq) => self.cmp(op, (lhs_val, lhs_ty), (rhs_val, rhs_ty)),
            x => Err(format!("Unknown binary operator: `{}`", x)),
        }
    }

    fn codegen_unop(&mut self, op: Operator, rhs: Node) -> ExprResult<'ctx> {
        use Operator::*;

        let rhs_ty = rhs.as_expr().ty().unwrap();
        let rhs_val = self.codegen_node(rhs)?.value()?;
        match op {
            Sub => self.neg((rhs_val, rhs_ty)),
            x => Err(format!("Unknown unary operator: `{}`", x)),
        }
    }

    fn codegen_call(&mut self, name: &str, args: Vec<Node>) -> Result<Option<BasicValueEnum<'ctx>>, String> {
        // Look up the function. Error if it's not been defined.
        let func = self.module.get_function(name).ok_or(format!("Unknown function call: {}", name))?;

        // Codegen the call args
        let mut args_code = Vec::with_capacity(args.len());
        for arg in args {
            args_code.push((self.codegen_node(arg)?.value()?).into());
        }

        // Build the call instruction
        let call_val = self.builder.build_call(func, &args_code, &("call_".to_owned() + name));

        // If func has a non-void return type, it will produce a call_val that is
        // converted into a BasicValueEnum. Otherwise it becomes an InstructionValue,
        // which we ignore.
        Ok(match call_val.try_as_basic_value() {
            Either::Left(v) => Some(v),
            Either::Right(_) => None,
        })
    }

    // if then optional else
    fn codegen_cond(
        &mut self, cond_expr: Node, then_block: Node, else_block: Option<Box<Node>>, ty: &Type,
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
        let cond_val = self.codegen_node(cond_expr)?.value()?.into_int_value();
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
        self.builder.build_conditional_branch(cond_bool, then_bb, else_bb);

        // Point the builder at the end of the empty then block
        self.builder.position_at_end(then_bb);

        // Codegen the then block. Save the last value for phi.
        let then_val = match self.codegen_node(then_block)? {
            Some(v) => v,
            None => undef_val,
        };

        // Make sure the consequent returns to the end block after its
        // execution. Don't forget to reset `then_bb` in case codegen moved it.
        self.builder.build_unconditional_branch(end_bb);
        then_bb = self.builder.get_insert_block().ok_or("Can't reset `then` block")?;

        // Point the builder at the end of the empty else/end block
        self.builder.position_at_end(else_bb);

        let val;
        // Codegen the else block if we have one
        if let Some(else_block) = else_block {
            // Codegen the else block. Save the last value for phi.
            let else_val = match self.codegen_node(*else_block)? {
                Some(v) => v,
                None => undef_val,
            };

            // Make sure the alternative returns to the end block after its
            // execution. Don't forget to reset `then_bb` in case codegen moved it.
            self.builder.build_unconditional_branch(end_bb);
            else_bb = self.builder.get_insert_block().ok_or("Can't reset `else` block")?;

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

    fn codegen_block(&mut self, list: Vec<Node>) -> Result<Option<BasicValueEnum<'ctx>>, String> {
        self.symbol_table.enter_scope();

        let mut node_val = None;
        for node in list {
            node_val = self.codegen_node(node)?;
        }

        self.symbol_table.leave_scope();

        Ok(node_val)
    }

    fn codegen_index(&mut self, binding: Node, idx: Node) -> ExprResult<'ctx> {
        let (binding_name, element_ptr) = self.get_array_element(binding, idx)?;
        Ok(self.builder.build_load(element_ptr, &("index.".to_owned() + binding_name.as_str())))
    }

    // Codegen variable initializers. Match combinations of init presence and type. When
    // init is None, initialize with 0.
    fn codegen_var_init(&mut self, ty: &Type, init: Option<Box<Node>>) -> ExprResult<'ctx> {
        let init_code = match (ty, init) {
            (_, Some(init)) => {
                if init.as_expr().ty().as_ref() == Some(ty) {
                    self.codegen_node(*init)?
                } else {
                    unreachable!("void type for init expr in `codegen_let()`");
                }
            },
            (int8_types!() | Type::Char, None) => {
                Some(self.context.i8_type().const_zero().as_basic_value_enum())
            },
            (int16_types!(), None) => Some(self.context.i16_type().const_zero().as_basic_value_enum()),
            (int32_types!(), None) => Some(self.context.i32_type().const_zero().as_basic_value_enum()),
            (int64_types!(), None) => Some(self.context.i64_type().const_zero().as_basic_value_enum()),
            (Type::Float, None) => Some(self.context.f32_type().const_zero().as_basic_value_enum()),
            (Type::Double, None) => Some(self.context.f64_type().const_zero().as_basic_value_enum()),
            (Type::Bool, None) => Some(self.context.bool_type().const_zero().as_basic_value_enum()),
            (Type::Void | Type::Array(..) | Type::Comp(_), None) => {
                unreachable!("void/invalid type for init annotation in `codegen_let()`")
            },
        };
        init_code.value()
    }

    // Helper to create an alloca in the entry block for local variables
    fn create_entry_block_alloca(&self, name: &str, ty: &Type, func: &FunctionValue) -> PointerValue<'ctx> {
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
            Type::Void => {
                unreachable!("void type for stack variable in `create_entry_block_alloca()`")
            },
            Type::Bool => builder.build_alloca(self.context.bool_type(), name),
            Type::Array(ty, sz) => {
                let array_ty = match self.get_llvm_ty(ty.as_ref().clone()) {
                    AnyTypeEnum::FloatType(ty) => (ty.as_basic_type_enum(), sz),
                    AnyTypeEnum::IntType(ty) => (ty.as_basic_type_enum(), sz),
                    _ => todo!(),
                };
                builder.build_alloca(
                    array_ty.0.array_type((*array_ty.1).try_into().expect("this is embarrassing")),
                    name,
                )
            },
            Type::Comp(_) => todo!(),
        }
    }

    // Helper to fetch a pointer to an array element
    fn get_array_element(
        &mut self, binding: Node, idx: Node,
    ) -> Result<(String, PointerValue<'ctx>), String> {
        // Extract the name of the ident in `binding`
        //
        // TODO: This could be something other than an ident in the future
        let binding = binding.as_expr();
        let name = match binding {
            Expression::Ident { ref name, .. } => name,
            _ => unreachable!("name missing for array index"),
        };

        // Get the allocated array ptr
        let array_ptr = self
            .symbol_table
            .get(name)
            .unwrap_or_else(|| unreachable!("codegen failed to resolve array name `{}`", name))
            .pointer()
            .expect("missing pointer on symbol");

        // Codegen the index
        let idx = self
            .codegen_node(idx)?
            .unwrap_or_else(|| unreachable!("missing value in index of `{}`", name))
            .into_int_value();

        let zero = self.context.i32_type().const_zero();
        unsafe {
            Ok((
                name.to_owned(),
                self.builder.build_in_bounds_gep(array_ptr, &[zero, idx], "array.index.gep"),
            ))
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
            Type::Array(ty, size) => {
                let size = size.try_into().expect("this is embarrassing");
                match self.get_llvm_ty(*ty) {
                    AnyTypeEnum::ArrayType(ty) => ty.array_type(size).as_any_type_enum(),
                    AnyTypeEnum::FloatType(ty) => ty.array_type(size).as_any_type_enum(),
                    AnyTypeEnum::IntType(ty) => ty.array_type(size).as_any_type_enum(),
                    _ => todo!(),
                }
            },
            Type::Comp(_) => todo!(),
        }
    }
}

// This is a little wonky. Allows us to return a file path for main or a string for the
// test suite.
pub enum CodegenResult {
    FilePath(PathBuf),
    Ir(String),
}

impl CodegenResult {
    pub fn as_file_path(self) -> PathBuf {
        match self {
            CodegenResult::FilePath(b) => b,
            CodegenResult::Ir(_) => unimplemented!("Expecting file path"),
        }
    }

    pub fn as_ir_string(self) -> String {
        match self {
            CodegenResult::FilePath(_) => unimplemented!("Expecting IR string"),
            CodegenResult::Ir(ir) => ir,
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
