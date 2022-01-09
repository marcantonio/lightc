use inkwell::{context::Context, passes::PassManager, OptimizationLevel};
use lightc::*;
use std::fs;

fn main() {
    let mut tokens: Vec<Token> = vec![];
    let code = fs::read_to_string("/home/mas/Code/lightc/mm.lt").expect("Error opening file");

    tokens.append(&mut lexer(&code).expect("Error lexing"));
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
    let fpm = PassManager::create(&module);
    let mut ir_gen = IrGenerator::new(&context, &builder, &module, &fpm);
    let main = ir_gen.generate(&ast).expect("Compiler error:");
    println!("main() IR:");
    main.print_to_stderr();
    println!();

    let ee = module.create_jit_execution_engine(OptimizationLevel::None).unwrap();

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
