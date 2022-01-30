use inkwell::{context::Context, passes::PassManager, values::AnyValue};
use lightc::ir_generator::IrGenerator;
use lightc::lexer::Lexer;
use lightc::parser::Parser;

// I don't know if this test is worth the trouble...
#[test]
fn test_ir_gen_basic() {
    let input = "fn main() { 19 + 21 + 40 }";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = parser.parse().unwrap();

    let context = Context::create();
    let builder = context.create_builder();
    let module = context.create_module("main_mod");
    let fpm = PassManager::create(&module);
    let mut ir_gen = IrGenerator::new(&context, &builder, &module, &fpm);
    let main = ir_gen.generate(&ast).unwrap();

    let expected = "define double @main() {
entry:
  ret double 8.000000e+01
}
";

    assert_eq!(main.print_to_string().to_string(), expected);
}

// TODO: Re-enable later. The cond gets optimized out.
#[test]
#[ignore]
fn test_ir_gen_cond() {
    let input = "fn test(x) { if x < 2 { 1 } else { 2 } } fn main() { test(2) }";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = parser.parse().unwrap();

    let context = Context::create();
    let builder = context.create_builder();
    let module = context.create_module("main_mod");
    let fpm = PassManager::create(&module);
    let mut ir_gen = IrGenerator::new(&context, &builder, &module, &fpm);
    let main = ir_gen.generate(&ast).unwrap();

    let expected = "foo";

    assert_eq!(main.print_to_string().to_string(), expected);
}

#[test]
fn test_ir_gen_assign_unknown() {
    let input = "fn main() { x = 1 }";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = parser.parse().unwrap();

    let context = Context::create();
    let builder = context.create_builder();
    let module = context.create_module("main_mod");
    let fpm = PassManager::create(&module);
    let mut ir_gen = IrGenerator::new(&context, &builder, &module, &fpm);

    assert_eq!(ir_gen.generate(&ast), Err("Unknown variable in assignment: x".to_string()));
}

#[test]
fn test_ir_gen_assign_bad_lval() {
    let input = "fn main(x) { x + 1 = 1 }";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = parser.parse().unwrap();

    let context = Context::create();
    let builder = context.create_builder();
    let module = context.create_module("main_mod");
    let fpm = PassManager::create(&module);
    let mut ir_gen = IrGenerator::new(&context, &builder, &module, &fpm);

    assert_eq!(ir_gen.generate(&ast), Err("Expected LHS to be a variable for assignment".to_string()));
}
