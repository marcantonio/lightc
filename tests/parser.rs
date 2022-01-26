use lightc::lexer::Lexer;
use lightc::parser::*;

fn ast_to_string(ast: &[AstNode]) -> String {
    if ast.len() == 1 {
        return ast[0].to_string();
    }

    let mut s = String::new();
    for node in ast {
        s = s + &node.to_string() + "\n";
    }
    s
}

#[test]
fn test_parser_single_num() {
    let input = "19";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "19";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);
}

#[test]
fn test_parser_two_num_expr() {
    let input = "19 + 21";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(+ 19 21)";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);
}

#[test]
fn test_parser_three_num_expr() {
    let input = "19 + 21 + -40";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(+ (+ 19 21) (- 40))";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);
}

#[test]
fn test_parser_precedence_expr() {
    let input = "19 + 21 * 40";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(+ 19 (* 21 40))";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);

    let input = "19 * 21 - 40";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(- (* 19 21) 40)";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);

    let input = "19 - 21 + 40";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(+ (- 19 21) 40)";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);

    let input = "19 - 21 * 20 + 40";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(+ (- 19 (* 21 20)) 40)";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);
}

#[test]
fn test_parser_right_assoc_expr() {
    let input = "19 ^ 21 ^ 40";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(^ 19 (^ 21 40))";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);

    let input = "19 ^ 21 + 40";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(+ (^ 19 21) 40)";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);

    let input = "19 ^ 21 ^ 40 / 2";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(/ (^ 19 (^ 21 40)) 2)";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);
}

#[test]
fn test_parser_multiple_exprs() {
    let input = "19 ^ 21 ^ 40 19 - 21 * 20 + 40";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(^ 19 (^ 21 40))\n(+ (- 19 (* 21 20)) 40)\n";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);
}

#[test]
fn test_parser_paren_precedence_expr() {
    let input = "(19 + 21) / 40";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(/ (+ 19 21) 40)";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);
}

#[test]
fn test_parser_paren_complex_precedence_expr() {
    let input = "3 * ((19 + 21) - 5) / 40";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(/ (* 3 (- (+ 19 21) 5)) 40)";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);
}

#[test]
fn test_parser_excessive_parens_expr() {
    let input = "(((0)))";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "0";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);
}

#[test]
fn test_parser_simple_ident_expr() {
    let input = "19 + a + 40";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(+ (+ 19 a) 40)";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);
}

#[test]
fn test_parser_nullary_call_expr() {
    let input = "a()";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(a)";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);
}

#[test]
fn test_parser_call_expr() {
    let input = "a(b, c)";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(a b c)";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);
}

#[test]
fn test_parser_call_with_expr_as_arg() {
    let input = "a(b + 1, c - 2 / 4)";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(a (+ b 1) (- c (/ 2 4)))";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);
}

#[test]
fn test_parser_call_with_call_as_arg() {
    let input = "a(b(c))";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(a (b c))";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);
}

#[test]
fn test_parser_func_def() {
    let input = "\
fn a(b, c) {
    19 + a + 40
}
";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(define (a b c) (+ (+ 19 a) 40))";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);
}

#[test]
fn test_parser_func_def_multi_line() {
    let input = "\
fn a(b, c) {
    19 + a + 40
    b + a
}
";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(define (a b c) (+ (+ 19 a) 40) (+ b a))";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);
}

#[test]
fn test_parser_empty_func_def() {
    let input = "fn a() {}";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(define (a))";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);
}

#[test]
fn test_parser_gt_lt() {
    let input = "a + b > 40";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(> (+ a b) 40)";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);

    let input = "a < b / 40";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(< a (/ b 40))";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);
}

#[test]
fn test_parser_extern() {
    let input = "extern cos(x)";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(define (cos x))";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);
}

#[test]
fn test_parser_if_only() {
    let input = "if a > b { foo }";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    println!("{:?}", tokens);
    let parser = Parser::new(&tokens);
    let ast = "(if (> a b) foo)";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);
}

#[test]
fn test_parser_if_else() {
    let input = "if a > b { foo } else { bar }";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(if (> a b) foo bar)";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);

    let input = "if a > b { foo } else if a < b { bar } else { baz }";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(if (> a b) foo (if (< a b) bar baz))";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);
}

#[test]
fn test_parser_for() {
    let input = "for let x = 1; x < 10; 1 { foo }";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    println!("{:?}", tokens);
    let parser = Parser::new(&tokens);
    let ast = "(for (let x 1) (< x 10) 1 foo)";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);
}

#[test]
fn test_parser_unary() {
    let input = "-21";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(- 21)";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);

    let input = "-a * 2";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(* (- a) 2)";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);

    let input = "3 - -21";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(- 3 (- 21))";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);

    let input = "--21";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(- (- 21))";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);
}

#[test]
fn test_parser_logical_ops() {
    let input = "x == 1";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(== x 1)";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);

    let input = "x && 1";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(&& x 1)";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);

    let input = "x || 1";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(|| x 1)";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);

    let input = "x == 1 && y == 2 || z == 3";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(|| (&& (== x 1) (== y 2)) (== z 3))";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);

    let input = "x == 1 && (y == 2 || z == 3)";
    let tokens = Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(&& (== x 1) (|| (== y 2) (== z 3)))";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);
}
