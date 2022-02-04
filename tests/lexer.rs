use lightc::lexer::Symbol::*;
use lightc::lexer::Token::*;
use lightc::lexer::*;

#[test]
fn test_lexer_full() {
    let input = "\
extern cos(x)

fn arith(x, y) {
    let result_val = (x + y) * 4 / 4
    a > b
    result_val
}

fn main() {
    // Call arith()
    let a = arith(36, 434)
    printf(a)
}
";

    let output = [
        Extern,
        Ident("cos".to_string()),
        OpenParen,
        Ident("x".to_string()),
        CloseParen,
        Fn,
        Ident("arith".to_string()),
        OpenParen,
        Ident("x".to_string()),
        Comma,
        Ident("y".to_string()),
        CloseParen,
        OpenBrace,
        Let,
        Ident("result_val".to_string()),
        Op(Symbol::Assign),
        OpenParen,
        Ident("x".to_string()),
        Op(Plus),
        Ident("y".to_string()),
        CloseParen,
        Op(Mult),
        Int(4),
        Op(Div),
        Int(4),
        Ident("a".to_string()),
        Op(Gt),
        Ident("b".to_string()),
        Ident("result_val".to_string()),
        CloseBrace,
        Fn,
        Ident("main".to_string()),
        OpenParen,
        CloseParen,
        OpenBrace,
        Let,
        Ident("a".to_string()),
        Op(Symbol::Assign),
        Ident("arith".to_string()),
        OpenParen,
        Int(36),
        Comma,
        Int(434),
        CloseParen,
        Ident("printf".to_string()),
        OpenParen,
        Ident("a".to_string()),
        CloseParen,
        CloseBrace,
    ];

    let lexer = Lexer::new(input);
    assert_eq!(lexer.collect::<Result<Vec<_>, _>>().unwrap(), &output);
}

#[test]
fn test_lexer_err_num() {
    let input = "let foo = 1b4";
    assert_eq!(
        Lexer::new(input).collect::<Result<Vec<_>, _>>(),
        Err(LexError::InvalidNum)
    );
}

#[test]
fn test_lexer_multiline_comment() {
    let input = "\
let foo = 14
// line1
// line2
foo
";
    let output = [
        Let,
        Ident("foo".to_string()),
        Op(Symbol::Assign),
        Int(14),
        Ident("foo".to_string()),
    ];
    assert_eq!(
        Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap(),
        &output
    );
}

#[test]
fn test_lexer_trailing_comment() {
    let input = "\
let foo = 13
// line2";
    let output = [Let, Ident("foo".to_string()), Op(Symbol::Assign), Int(13)];
    assert_eq!(
        Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap(),
        &output
    );
}

#[test]
fn test_lexer_if_else() {
    let input = "\
if x > -3 {
    print(x)
} else {
    exit()
}
";
    let output = [
        If,
        Ident("x".to_string()),
        Op(Gt),
        Op(Minus),
        Int(3),
        OpenBrace,
        Ident("print".to_string()),
        OpenParen,
        Ident("x".to_string()),
        CloseParen,
        CloseBrace,
        Else,
        OpenBrace,
        Ident("exit".to_string()),
        OpenParen,
        CloseParen,
        CloseBrace,
    ];
    assert_eq!(
        Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap(),
        &output
    );
}

#[test]
fn test_lexer_for() {
    let input = "\
for let x = 1; x < 10; 1 {
    print(x)
}
";
    let output = [
        For,
        Let,
        Ident("x".to_string()),
        Op(Symbol::Assign),
        Int(1),
        Semicolon,
        Ident("x".to_string()),
        Op(Lt),
        Int(10),
        Semicolon,
        Int(1),
        OpenBrace,
        Ident("print".to_string()),
        OpenParen,
        Ident("x".to_string()),
        CloseParen,
        CloseBrace,
    ];
    assert_eq!(
        Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap(),
        &output
    );
}

#[test]
fn test_logical_ops() {
    let input = "x == 1";
    let output = [Ident("x".to_string()), Op(Eq), Int(1)];
    assert_eq!(
        Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap(),
        &output
    );

    let input = "x && 1";
    let output = [Ident("x".to_string()), Op(And), Int(1)];
    assert_eq!(
        Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap(),
        &output
    );

    let input = "x || 1";
    let output = [Ident("x".to_string()), Op(Or), Int(1)];
    assert_eq!(
        Lexer::new(input).collect::<Result<Vec<_>, _>>().unwrap(),
        &output
    );
}
