use inkwell::passes::PassManager;
use inkwell::values::FunctionValue;
use inkwell::{context::Context, values::AnyValue};
use insta::assert_yaml_snapshot;
use insta::glob;
use std::fs;

use lightc::ir_generator::IrGenerator;
use lightc::lexer::Lexer;
use lightc::parser::Parser;

// This is how we "deserialize" FunctionValue to work with insta
fn ir_to_string(ir: Result<FunctionValue, String>) -> String {
    match ir {
        Ok(ir) => ir.print_to_string().to_string(),
        Err(err) => err,
    }
}

#[test]
fn test_ir_gen() {
    glob!("inputs/ir_gen/*.input", |path| {
        let input = fs::read_to_string(path).unwrap();
        let tokens = Lexer::new(&input).collect::<Result<Vec<_>, _>>().unwrap();
        let parser = Parser::new(&tokens);
        let ast = parser.parse().unwrap();

        let context = Context::create();
        let builder = context.create_builder();
        let module = context.create_module("main_mod");
        let fpm = PassManager::create(&module);
        let mut ir_gen = IrGenerator::new(&context, &builder, &module, &fpm);

        assert_yaml_snapshot!(ir_to_string(ir_gen.generate(&ast)));
    });
}
