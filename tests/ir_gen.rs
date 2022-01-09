use inkwell::{context::Context, passes::PassManager};
use light::*;

// I don't know if this test is worth the trouble...
#[test]
fn test_ir_gen() {
    let input = "fn main() { 19 + 21 + 40 }";
    let tokens = lexer(input).unwrap();
    let parser = Parser::new(&tokens);
    let ast = parser.parse().unwrap();

    let context = Context::create();
    let builder = context.create_builder();
    let module = context.create_module("main");
    let fpm = PassManager::create(&module);
    let mut ir_gen = IrGenerator::new(&context, &builder, &module, &fpm);

    let expected = "define double @main() {
entry:
  ret double 8.000000e+01
}
";

    assert_eq!(ir_gen.generate(&ast, true).unwrap().unwrap(), expected);
}

//ready> def test(x) (1+2+x)*(x+(1+2));
