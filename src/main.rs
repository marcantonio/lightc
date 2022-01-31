pub mod ir_generator;
pub mod lexer;
pub mod parser;

use crate::ir_generator::IrGenerator;
use crate::lexer::Lexer;
use crate::parser::Parser;
use inkwell::{
    context::Context,
    passes::PassManager,
    targets::{InitializationConfig, Target, TargetMachine},
    OptimizationLevel,
};
use std::{fs, process::Command};

fn main() {
    lightc::load_externs();

    let code =
        fs::read_to_string("/home/mas/Code/lightc/examples/mm.lt").expect("Error opening file");

    let lexer = Lexer::new(&code);
    let tokens = lexer.collect::<Result<Vec<_>, _>>().expect("Error lexing");
    println!("tokens: {:?}", tokens);
    println!();

    let parser = Parser::new(&tokens);
    let ast = parser.parse().expect("Error parsing");
    println!("ast:");
    for node in &ast {
        println!("{}", node);
    }
    println!();

    let context = Context::create();
    let builder = context.create_builder();
    let module = context.create_module("main_mod");

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

    let fpm = PassManager::create(&module);
    let mut ir_gen = IrGenerator::new(&context, &builder, &module, &fpm);
    let main = ir_gen.generate(&ast).expect("Compiler error");

    let path = std::path::Path::new("mm.ll");
    module.print_to_file(path).expect("Error writing tmp IR");

    Command::new("clang")
        .arg("mm.ll")
        .spawn()
        .expect("Error compiling");

    println!("main() IR:");
    main.print_to_stderr();
    println!();

    let ee = module
        .create_jit_execution_engine(OptimizationLevel::None)
        .unwrap();

    let f = unsafe { ee.get_function::<unsafe extern "C" fn() -> f64>("main") };
    match f {
        Ok(f) => unsafe {
            let ret = f.call();
            println!("main: {:?}", ret);
        },
        Err(e) => {
            println!("Execution error: {}", e);
        }
    };
}
