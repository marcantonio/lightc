use either::Either;
use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::passes::PassManager;
use inkwell::targets::{FileType, InitializationConfig, Target, TargetMachine};
use inkwell::types::{AnyType, AnyTypeEnum, BasicMetadataTypeEnum, BasicType, BasicTypeEnum};
use inkwell::values::{BasicValue, BasicValueEnum, FunctionValue, InstructionOpcode, PointerValue};
use inkwell::{IntPredicate, OptimizationLevel};
use std::path::PathBuf;
use std::process;

use codegen_symbol::CodegenSymbol;
use common::symbol_table::Symbolic;
use common::{CliArgs, Literal, Operator, Prototype, Symbol, SymbolTable, Type};
use lower::hir::{VisitableNode, Visitor};
use lower::{hir, Hir};

#[macro_use]
extern crate common;

mod codegen_symbol;
#[macro_use]
mod macros;
mod jit_externs;
mod ops;
#[cfg(test)]
mod tests;

// Generate IR for the HIR

pub struct Codegen<'ctx> {
    context: &'ctx Context,
    builder: Builder<'ctx>,
    module: Module<'ctx>,
    fpm: PassManager<FunctionValue<'ctx>>,
    symbol_table: SymbolTable<CodegenSymbol<'ctx>>,
    main: Option<FunctionValue<'ctx>>,
    opt_level: usize,
    no_verify: bool,
    module_name: String,
    active_loop_exit_block: Option<BasicBlock<'ctx>>,
}

impl<'ctx> Codegen<'ctx> {
    pub fn run(
        hir: Hir<hir::Node>, module_name: &str, symbol_table: SymbolTable<Symbol>, build_dir: PathBuf,
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
            module_name: module_name.to_owned(),
            active_loop_exit_block: None,
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
        module_file.push(module_name);
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
    pub fn walk(&mut self, hir: Hir<hir::Node>) -> Result<(), String> {
        let (nodes, prototypes) = hir.into_components();

        // Do structs first so all types are complete
        self.codegen_all_structs()?;

        // Do prototypes next so declaration order doesn't matter
        self.codegen_all_prototypes(prototypes)?;

        // Do the rest
        for node in nodes {
            node.accept(self)?;
        }

        // Ensure main exists if this is a standalone executable
        if self.module_name == "main" && self.main.is_none() {
            Err("Function main() required in `main` module".to_string())
        } else {
            Ok(())
        }
    }

    // Codegen all structs to ensure that declaration order doesn't matter
    fn codegen_all_structs(&self) -> Result<(), String> {
        let structs = self.symbol_table.filter(|sym| sym.kind() == "Struct");
        let struct_parts = structs
            .iter()
            .map(|sym| {
                let sym = sym.inner();
                let field_tys: Vec<Type> = sym
                    .fields()
                    .unwrap_or_else(|| unreachable!("invalid node in struct list"))
                    .iter()
                    .map(|(_, ty)| Type::from(*ty))
                    .collect();
                (self.context.opaque_struct_type(&sym.name), field_tys)
            })
            .collect::<Vec<_>>();

        for (opaque_struct, field_tys) in struct_parts {
            let fields = field_tys
                .iter()
                .map(|ty| self.get_llvm_basic_type(ty))
                .collect::<Result<Vec<_>, String>>()?;
            opaque_struct.set_body(&fields, false);
        }

        Ok(())
    }

    // Codegen all prototypes to ensure that call order doesn't matter
    fn codegen_all_prototypes(&self, prototypes: Vec<Prototype>) -> Result<(), String> {
        for proto in prototypes {
            // Get LLVM types for function args
            let mut args_types = vec![];
            for (_, arg_ty) in proto.params() {
                let llvm_ty = match self.get_llvm_any_type(arg_ty)? {
                    AnyTypeEnum::FloatType(ty) => BasicMetadataTypeEnum::FloatType(ty),
                    AnyTypeEnum::IntType(ty) => BasicMetadataTypeEnum::IntType(ty),
                    AnyTypeEnum::ArrayType(ty) => BasicMetadataTypeEnum::ArrayType(ty),
                    AnyTypeEnum::StructType(ty) => BasicMetadataTypeEnum::StructType(ty),
                    AnyTypeEnum::PointerType(ty) => BasicMetadataTypeEnum::PointerType(ty),
                    ty => unreachable!(
                        "unsupported argument type `{}` in prototype `{}()`",
                        ty.print_to_string(),
                        proto.name(),
                    ),
                };
                args_types.push(llvm_ty);
            }

            // Generate function based on return type
            let func_type = match self.get_llvm_any_type(proto.ret_ty())? {
                AnyTypeEnum::FloatType(ty) => ty.fn_type(&args_types, false),
                AnyTypeEnum::IntType(ty) => ty.fn_type(&args_types, false),
                AnyTypeEnum::VoidType(ty) => ty.fn_type(&args_types, false),
                AnyTypeEnum::StructType(ty) => ty.fn_type(&args_types, false),
                AnyTypeEnum::PointerType(ty) => ty.fn_type(&args_types, false),
                ty => unreachable!(
                    "unsupported return type `{}` in prototype `{}()`",
                    ty.print_to_string(),
                    proto.name(),
                ),
            };

            // Add function to current module's symbol table. Defaults to external
            // linkage with None.
            let func = self.module.add_function(proto.name(), func_type, None);

            // Name all args
            func.get_param_iter().enumerate().for_each(|(i, arg)| {
                arg.set_name(&proto.params()[i].0);
            });
        }
        Ok(())
    }

    // Codegen variable initializers. Match combinations of init presence and type. When
    // init is None, initialize with 0.
    fn codegen_var_init(
        &mut self, ty: &Type, init: Option<hir::Node>,
    ) -> Result<BasicValueEnum<'ctx>, String> {
        let init_code = match (ty, init) {
            (_, Some(init)) => {
                if init.ty() == ty {
                    self.visit_node(init)?
                } else {
                    unreachable!("void type for init expr in `codegen_var_init()`");
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
            (Type::Void | Type::SArray(..) | Type::Comp(_) | Type::Ptr(_), None) => {
                unreachable!("void/invalid type for init annotation in `codegen_var_init()`")
            },
        };
        init_code.expr_value()
    }

    // Helper to create an alloca in the entry block for local variables
    fn create_entry_block_alloca(
        &self, name: &str, ty: &Type, func: &FunctionValue,
    ) -> Result<PointerValue<'ctx>, String> {
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
        Ok(match ty {
            int8_types!() | Type::Char => builder.build_alloca(self.context.i8_type(), name),
            int16_types!() => builder.build_alloca(self.context.i16_type(), name),
            int32_types!() => builder.build_alloca(self.context.i32_type(), name),
            int64_types!() => builder.build_alloca(self.context.i64_type(), name),
            Type::Float => builder.build_alloca(self.context.f32_type(), name),
            Type::Double => builder.build_alloca(self.context.f64_type(), name),
            Type::Bool => builder.build_alloca(self.context.bool_type(), name),
            Type::SArray(ty, sz) => {
                let sarray_ty = match self.get_llvm_any_type(&ty.as_ref().clone())? {
                    AnyTypeEnum::FloatType(ty) => (ty.as_basic_type_enum(), sz),
                    AnyTypeEnum::IntType(ty) => (ty.as_basic_type_enum(), sz),
                    _ => todo!(),
                };
                builder.build_alloca(
                    sarray_ty.0.array_type(
                        (*sarray_ty.1)
                            .try_into()
                            .map_err(|err| format!("failed to convert array index: `{}`", err))?,
                    ),
                    name,
                )
            },
            Type::Comp(_) => {
                let struct_ty = self.get_llvm_basic_type(ty)?;
                builder.build_alloca(struct_ty, name)
            },
            Type::Ptr(ty) => {
                let ptr_ty =
                    self.get_llvm_basic_type(ty)?.into_struct_type().ptr_type(inkwell::AddressSpace::Generic);
                builder.build_alloca(ptr_ty, name)
            },
            Type::Void => {
                unreachable!("void type for stack variable in `create_entry_block_alloca()`")
            },
        })
    }

    // Helper to fetch a pointer to an array element
    fn get_array_element(&mut self, array: hir::Node, idx: hir::Node) -> Result<PointerValue<'ctx>, String> {
        use hir::node::Kind::*;

        // Codegen the array value
        let array_ptr = match array.kind {
            // TODO: As an optimization, when an Ident is found, pull the pointer out of
            // the symbol table rather than calling visit_node(). This will skip the
            // generated load instruction
            Ident { .. } | FSelector { .. } => {
                let value =
                    self.visit_node(array)?.unwrap_or_else(|| unreachable!("can't find struct pointer"));
                // XXX use derive_composite_pointer!() here?
                let inst = value.as_instruction_value().unwrap();
                inst.get_operand(0).unwrap().left().unwrap().into_pointer_value()
            },
            _ => unreachable!("unsupported type for array index"),
        };

        // Codegen the index
        let idx =
            self.visit_node(idx)?.unwrap_or_else(|| unreachable!("missing value in index")).into_int_value();

        let zero = self.context.i32_type().const_zero();

        unsafe { Ok(self.builder.build_in_bounds_gep(array_ptr, &[zero, idx], "array.index.gep")) }
    }

    // Help to find the pointer to a struct element
    fn get_struct_element(&mut self, comp: hir::Node, idx: u32) -> Result<PointerValue<'ctx>, String> {
        use hir::node::Kind::*;

        // Codegen the composite value
        let comp_value = match comp.clone().kind {
            Let { ref name, .. } => {
                self.visit_node(comp)?;
                self.symbol_table.get(name).unwrap().pointer().unwrap().as_basic_value_enum()
            },
            Ident { .. } | FSelector { .. } => {
                self.visit_node(comp)?.unwrap_or_else(|| unreachable!("can't find struct pointer"))
            },
            _ => unimplemented!("unsupported composite type for selector"),
        };

        // If the composite is already a pointer, as in the case of chained fields, don't
        // try to coerce into a pointer. Otherwise derive pointer from load
        // instruction. In some cases the loaded value is a pointer. If not, derive as
        // well.
        let struct_ptr = if comp_value.is_pointer_value() {
            let comp_ptr = comp_value.into_pointer_value();
            let comp_load = self.builder.build_load(comp_ptr, "");
            if comp_load.is_pointer_value() {
                comp_load.into_pointer_value()
            } else {
                derive_composite_pointer!(comp_load)
            }
        } else {
            derive_composite_pointer!(comp_value)
        };

        Ok(self
            .builder
            .build_struct_gep(struct_ptr, idx, "struct.field.gep")
            .map_err(|_| "failed to build struct GEP")?)
    }

    fn get_llvm_basic_type(&self, ty: &Type) -> Result<BasicTypeEnum<'ctx>, String> {
        Ok(match ty {
            int8_types!() | Type::Char => self.context.i8_type().as_basic_type_enum(),
            int16_types!() => self.context.i16_type().as_basic_type_enum(),
            int32_types!() => self.context.i32_type().as_basic_type_enum(),
            int64_types!() => self.context.i64_type().as_basic_type_enum(),
            Type::Float => self.context.f32_type().as_basic_type_enum(),
            Type::Double => self.context.f64_type().as_basic_type_enum(),
            Type::Bool => self.context.bool_type().as_basic_type_enum(),
            Type::SArray(element_ty, size) => {
                let size =
                    (*size).try_into().map_err(|err| format!("failed to convert sarray size: `{}`", err))?;
                match self.get_llvm_any_type(element_ty)? {
                    AnyTypeEnum::ArrayType(ty) => ty.array_type(size).as_basic_type_enum(),
                    AnyTypeEnum::FloatType(ty) => ty.array_type(size).as_basic_type_enum(),
                    AnyTypeEnum::IntType(ty) => ty.array_type(size).as_basic_type_enum(),
                    _ => todo!(),
                }
            },
            Type::Comp(name) => self
                .module
                .get_struct_type(name)
                .unwrap_or_else(|| {
                    unreachable!("missing struct definition for `{}` in `get_llvm_basic_type()`", name)
                })
                .as_basic_type_enum(),
            Type::Ptr(ptr_ty) => {
                let name = ptr_ty.get_comp_name();
                self.module
                    .get_struct_type(name)
                    .unwrap_or_else(|| {
                        unreachable!("missing struct definition for `{}` in `get_llvm_basic_type()`", name)
                    })
                    .ptr_type(inkwell::AddressSpace::Generic) // XXX right address space?
                    .as_basic_type_enum()
            },
            Type::Void => unreachable!("void can't be coerced into LLVM basic type"),
        })
    }

    fn get_llvm_any_type(&self, ty: &Type) -> Result<AnyTypeEnum<'ctx>, String> {
        Ok(match ty {
            Type::Void => self.context.void_type().as_any_type_enum(),
            _ => self.get_llvm_basic_type(ty)?.as_any_type_enum(),
        })
    }
}

impl<'ctx> hir::Visitor for Codegen<'ctx> {
    type AstNode = hir::Node;
    type Result = Result<Option<BasicValueEnum<'ctx>>, String>;

    fn visit_node(&mut self, node: Self::AstNode) -> Self::Result {
        if node.is_blank() {
            Ok(None)
        } else {
            node.accept(self)
        }
    }

    // for start; cond; step { body }
    fn visit_for(
        &mut self, start_name: String, start_antn: Type, start_expr: Option<hir::Node>, cond_expr: hir::Node,
        step_expr: hir::Node, body: hir::Node,
    ) -> Self::Result {
        let parent = self
            .builder
            .get_insert_block()
            .and_then(|x| x.get_parent())
            .ok_or_else(|| "Parent function not found when building loop".to_string())?;

        // Create entry alloca, codegen start expr, and store result
        let start_alloca = self.create_entry_block_alloca(&start_name, &start_antn, &parent)?;
        let start_code = self.codegen_var_init(&start_antn, start_expr)?;
        self.builder.build_store(start_alloca, start_code);

        // Create interstitial scope to protect the induction variable
        self.symbol_table.enter_scope();

        // Save new symbol with alloca
        let start_sym =
            CodegenSymbol::new_var(start_name.as_str(), &start_antn, &self.module_name, start_alloca);
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
        let cond_code = self.visit_node(cond_expr)?.expr_value()?.into_int_value();
        self.builder.build_conditional_branch(cond_code, body_bb, post_bb);

        // Generate all body expressions
        self.builder.position_at_end(body_bb);
        self.visit_node(body)?;
        self.builder.build_unconditional_branch(step_bb);

        // Generate step value, load the current induction variable from the stack, increment it by
        // step, and store it again. Body could have mutated it.
        self.builder.position_at_end(step_bb);
        let step_code = self.visit_node(step_expr)?;
        let cur = self.builder.build_load(start_alloca, &start_name);
        match start_antn {
            int_types!() => {
                let next = self.builder.build_int_add(
                    cur.into_int_value(),
                    step_code.expr_value()?.into_int_value(),
                    "for.int.step",
                );
                self.builder.build_store(start_alloca, next);
            },
            float_types!() => {
                let next = self.builder.build_float_add(
                    cur.into_float_value(),
                    step_code.expr_value()?.into_float_value(),
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

        Ok(None)
    }

    fn visit_loop(&mut self, body: hir::Node) -> Self::Result {
        let parent = self
            .builder
            .get_insert_block()
            .and_then(|x| x.get_parent())
            .ok_or_else(|| "Parent function not found when building loop".to_string())?;

        // Create body and post blocks
        let body_bb = self.context.append_basic_block(parent, "loop.body");
        let post_bb = self.context.append_basic_block(parent, "loop.post");

        // Jump from entry to body
        self.builder.build_unconditional_branch(body_bb);

        // Stash post_bb for possible break/next in body. Save old one
        let old_post_bb = self.active_loop_exit_block;
        self.active_loop_exit_block = Some(post_bb);

        // Generate all body expressions
        self.builder.position_at_end(body_bb);
        self.visit_node(body)?;

        // Restore old post_bb
        self.active_loop_exit_block = old_post_bb;

        // Loop around to the beginning unless the block ended in a break
        self.builder.build_unconditional_branch(body_bb);

        // Set insertion to after the loop
        self.builder.position_at_end(post_bb);

        Ok(None)
    }

    fn visit_break(&mut self) -> Self::Result {
        match self.active_loop_exit_block {
            Some(bb) => {
                // Jump out of active loop
                self.builder.build_unconditional_branch(bb);
                self.active_loop_exit_block = Some(bb);
                Ok(None)
            },
            None => Err("can't call `break` outside of loop".to_string()),
        }
    }

    fn visit_let(&mut self, name: String, antn: Type, init: Option<hir::Node>) -> Self::Result {
        let parent = self
            .builder
            .get_insert_block()
            .and_then(|x| x.get_parent())
            .ok_or_else(|| "Parent function not found when building let statement".to_string())?;

        let init_code = self.codegen_var_init(&antn, init)?;

        let init_alloca = self.create_entry_block_alloca(&name, &antn, &parent)?;
        self.builder.build_store(init_alloca, init_code);

        let sym = CodegenSymbol::new_var(name.as_str(), &antn, &self.module_name, init_alloca);
        self.symbol_table.insert(sym);

        Ok(None)
    }

    fn visit_fn(&mut self, proto: Prototype, body: Option<hir::Node>) -> Self::Result {
        let sym = self
            .symbol_table
            .get(proto.name())
            .unwrap_or_else(|| unreachable!("missing symbol in `codegen_func()` for `{}`", proto.name()))
            .inner()
            .clone();

        // Rather than call `codegen_proto()` here, we do it early in
        // `insert_prototypes()`. This ensures we can codegen a call before the
        // `codegen_func()` is called.
        let function = self
            .module
            .get_function(proto.name())
            .unwrap_or_else(|| unreachable!("missing function `{}` in module table", proto.name()));

        // If body is None assume call is an extern
        let body = match body {
            Some(body) => body,
            None => return Ok(None),
        };

        // Creates interstitial scope for the arguments in the function definition
        self.symbol_table.enter_scope();

        // Create new block for function
        let bb = self.context.append_basic_block(function, "entry");

        // Make sure the builder will insert new instructions at the end
        self.builder.position_at_end(bb);

        // Allocate space for the function's arguments on the stack
        for (i, arg) in function.get_param_iter().enumerate() {
            let (name, ty) = &proto.params()[i];
            let alloca = self.create_entry_block_alloca(name, ty, &function)?;
            self.builder.build_store(alloca, arg);
            self.symbol_table.insert(CodegenSymbol::new_var(name.as_str(), ty, &self.module_name, alloca));
        }

        let body_val = self.visit_node(body)?;

        // Build the return function based on the prototype's return value and the last statement
        match (proto.ret_ty(), body_val) {
            (rt, Some(v)) if rt != &Type::Void => self.builder.build_return(Some(&v)),
            (rt, None) if rt != &Type::Void => {
                return Err(format!("Function should return `{}` but last statement is void", rt))
            },
            _ => self.builder.build_return(None),
        };

        self.symbol_table.leave_scope();

        // Identify main
        if function.get_name().to_str().unwrap() == "main" {
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
                return Err(format!("Error compiling: {}", sym.name));
            }
        }
        Ok(None)
    }

    fn visit_next(&mut self) -> Self::Result {
        unimplemented!()
    }

    fn visit_lit(&mut self, value: Literal<hir::Node>, ty: Type) -> Self::Result {
        use Literal::*;

        let lit = match value {
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
                // Get inner LLVM type and codegen all element values
                let inner_llvm_ty =
                    self.get_llvm_basic_type(&inner_ty.as_ref().cloned().unwrap_or_default())?;
                let mut vals = Vec::with_capacity(elements.len());
                for el in elements {
                    vals.push(self.visit_node(el)?.unwrap());
                }

                // If emtpy, initialize to zero and return
                if vals.is_empty() {
                    return Ok(Some(self.get_llvm_basic_type(&ty)?.const_zero()));
                }

                // Otherwise, create typed array of vals
                match inner_llvm_ty {
                    BasicTypeEnum::FloatType(wrapped_ty) => {
                        let vals = vals.iter().map(|v| v.into_float_value()).collect::<Vec<_>>();
                        wrapped_ty.const_array(&vals).as_basic_value_enum()
                    },
                    BasicTypeEnum::IntType(wrapped_ty) => {
                        let vals = vals.iter().map(|v| v.into_int_value()).collect::<Vec<_>>();
                        wrapped_ty.const_array(&vals).as_basic_value_enum()
                    },
                    _ => todo!(),
                }
            },
            Comp(fields) => {
                let llvm_struct_type = self
                    .module
                    .get_struct_type(&ty.to_string())
                    .unwrap_or_else(|| unreachable!("can't find struct definition"));

                let values = fields
                    .into_iter()
                    .flat_map(|n| self.visit_node(n).transpose())
                    .collect::<Result<Vec<_>, String>>()?;

                llvm_struct_type.const_named_struct(&values).as_basic_value_enum()
            },
        };
        Ok(Some(lit))
    }

    fn visit_ident(&mut self, name: String, ty: Type) -> Self::Result {
        // Get the variable pointer and load from the stack
        let ptr = self
            .symbol_table
            .get(&name)
            .unwrap_or_else(|| unreachable!("codegen failed to resolve `{}`", name))
            .pointer()
            .expect("missing pointer on symbol");

        // Don't generate load if it's a pointer already
        if let Type::Ptr(_) = ty {
            Ok(Some(ptr.as_basic_value_enum()))
        } else {
            Ok(Some(self.builder.build_load(ptr, &name)))
        }
    }

    fn visit_binop(&mut self, op: Operator, lhs: hir::Node, rhs: hir::Node) -> Self::Result {
        use Operator::*;

        let lhs_ty = lhs.ty();
        let lhs_val = self.visit_node(lhs.clone())?.expr_value()?;
        let rhs_ty = rhs.ty();
        let rhs_val = self.visit_node(rhs.clone())?.expr_value()?;

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
            x => Err(format!("unknown binary operator: `{}`", x)),
        }
        .map(Some)
    }

    fn visit_unop(&mut self, op: Operator, rhs: hir::Node) -> Self::Result {
        use Operator::*;

        let rhs_ty = rhs.ty().clone();
        let rhs_val = self.visit_node(rhs)?.expr_value()?;
        match op {
            Sub => self.neg((rhs_val, &rhs_ty)).map(Some),
            x => Err(format!("unknown unary operator: `{}`", x)),
        }
    }

    fn visit_call(&mut self, name: String, args: Vec<hir::Node>) -> Self::Result {
        // Look up the function. Error if it's not been defined.
        let func = self.module.get_function(&name).ok_or(format!("unknown function call: {}", name))?;

        // Codegen the call args
        let mut args_code = Vec::with_capacity(args.len());
        for arg in args {
            args_code.push(self.visit_node(arg)?.expr_value()?.into());
        }

        // Build the call instruction
        let call_val = self.builder.build_call(func, &args_code, &("call_".to_owned() + &name));

        // If func has a non-void return type, it will produce a call_val that is
        // converted into a BasicValueEnum. Otherwise it becomes an InstructionValue,
        // which we ignore.
        Ok(match call_val.try_as_basic_value() {
            Either::Left(v) => Some(v),
            Either::Right(_) => None,
        })
    }

    fn visit_cond(
        &mut self, cond_expr: hir::Node, then_block: hir::Node, else_block: Option<hir::Node>, ty: Type,
    ) -> Self::Result {
        // Get the current function for insertion
        let parent = self
            .builder
            .get_insert_block()
            .and_then(|x| x.get_parent())
            .ok_or_else(|| "Parent function not found when building conditional".to_string())?;

        // Codegen expression. Will be optimized to a 0 or 1 if comparing
        // constants. Otherwise, the value will be IR to evaluate. Result will
        // be a 0 or 1. Then compare cond_val to 0. Result will be a 1 bit
        // "bool".
        let cond_val = self.visit_node(cond_expr)?.expr_value()?.into_int_value();
        let cond_bool = self.builder.build_int_compare(
            IntPredicate::NE,
            cond_val,
            self.context.bool_type().const_zero(),
            "if.cond.int",
        );

        // Create blocks for branches and after. The else block is just a
        // pointer to end if there's no else expression.
        let mut then_bb = self.context.append_basic_block(parent, "if.then");
        let merge_bb = self.context.append_basic_block(parent, "if.merge");
        let mut else_bb = merge_bb;
        if else_block.is_some() {
            else_bb = self.context.append_basic_block(parent, "if.else");
        }

        // Emits the entry conditional branch instructions
        self.builder.build_conditional_branch(cond_bool, then_bb, else_bb);

        // Point the builder at the end of the empty then block
        self.builder.position_at_end(then_bb);

        // Codegen the then block
        let then_val = self.visit_node(then_block)?;

        // Only jump to the merge block if we don't have a previous break instruction
        //if !then_bb.get_terminator().is_some_and(|t| t.get_opcode() == InstructionOpcode::Br) {
            self.builder.build_unconditional_branch(merge_bb);
        //}
        // Don't forget to reset `then_bb` in case codegen moved it
        then_bb = self.builder.get_insert_block().ok_or("can't reset `then` block")?;

        // Point the builder at the end of the empty else/end block
        self.builder.position_at_end(else_bb);

        // Codegen the else block if we have one
        let mut else_val = None;
        if let Some(else_block) = else_block {
            // Codegen the else block
            else_val = self.visit_node(else_block)?;

            // Only jump to the merge block if we don't have a previous break instruction
            //if !else_bb.get_terminator().is_some_and(|t| t.get_opcode() == InstructionOpcode::Br) {
                self.builder.build_unconditional_branch(merge_bb);
            //}

            // Don't forget to reset `else_bb` in case codegen moved it
            else_bb = self.builder.get_insert_block().ok_or("can't reset `else` block")?;

            // Point the builder at the end of the empty end block
            self.builder.position_at_end(merge_bb);
        }

        if let (Some(then_val), Some(else_val)) = (then_val, else_val) {
            let phi = make_phi_for_type!(self.builder, self.context, ty, "if.else.phi");
            phi.add_incoming(&[(&then_val, then_bb), (&else_val, else_bb)]);
            Ok(Some(phi.as_basic_value()))
        } else {
            Ok(None)
        }
    }

    fn visit_block(&mut self, list: Vec<hir::Node>) -> Self::Result {
        self.symbol_table.enter_scope();

        let mut node_val = None;
        for node in list {
            node_val = self.visit_node(node)?;
        }

        self.symbol_table.leave_scope();

        Ok(node_val)
    }

    fn visit_index(&mut self, array: hir::Node, idx: hir::Node) -> Self::Result {
        let element_ptr = self.get_array_element(array, idx)?;
        Ok(Some(self.builder.build_load(element_ptr, "array.index")))
    }

    fn visit_fselector(&mut self, comp: hir::Node, idx: u32) -> Self::Result {
        let field_ptr = self.get_struct_element(comp, idx)?;
        Ok(Some(self.builder.build_load(field_ptr, &format!("struct.{}", idx))))
    }
}

// This is a little wonky. Allows us to return a file path for main or a string for the
// test suite.
pub enum CodegenResult {
    FilePath(PathBuf),
    Ir(String),
}

impl CodegenResult {
    pub fn to_path(self) -> PathBuf {
        match self {
            CodegenResult::FilePath(b) => b,
            CodegenResult::Ir(_) => unimplemented!("Expecting file path"),
        }
    }

    pub fn to_ir_string(self) -> String {
        match self {
            CodegenResult::FilePath(_) => unimplemented!("Expecting IR string"),
            CodegenResult::Ir(ir) => ir,
        }
    }
}

// Like unwrap() but with a fixed error message. Necessary to allow call_expr to
// return an Option for void calls.
trait ExprValue<T> {
    type Result;

    fn expr_value(self) -> Result<T, Self::Result>;
}

impl<T> ExprValue<T> for Option<T> {
    type Result = String;

    fn expr_value(self) -> Result<T, Self::Result> {
        match self {
            Some(v) => Ok(v),
            None => Err("expecting expression, found statement".to_string()),
        }
    }
}
