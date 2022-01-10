use inkwell::{context::Context, passes::PassManager, values::AnyValue};
use lightc::ir_generator::IrGenerator;
use lightc::lexer::Lexer;
use lightc::parser::Parser;

// I don't know if this test is worth the trouble...
#[test]
fn test_ir_gen() {
    let input = "fn main() { 19 + 21 + 40 }";
    let tokens = Lexer {}.lex(input).unwrap();
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

//ready> def test(x) (1+2+x)*(x+(1+2));
