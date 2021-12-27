use light::*;

#[test]
fn test_lexer_full() {
    use Token::*;

    let input = "\
fn arith(x: u64, y: u64): u64 {
    let result = (x + y) * 4 / 4
    result
}

fn main() {
    // Call arith()
    let a = arith(36, 434)
    printf(a)
}
";

    let output = [
        Fn,
        Ident("arith".to_string()),
        OpenParen,
        Ident("x".to_string()),
        Colon,
        Type("u64".to_string()),
        Comma,
        Ident("y".to_string()),
        Colon,
        Type("u64".to_string()),
        CloseParen,
        Colon,
        Type("u64".to_string()),
        OpenBrace,
        Let,
        Ident("result".to_string()),
        Assign,
        OpenParen,
        Ident("x".to_string()),
        Op('+'),
        Ident("y".to_string()),
        CloseParen,
        Op('*'),
        Int(4),
        Op('/'),
        Int(4),
        Ident("result".to_string()),
        CloseBrace,
        Fn,
        Ident("main".to_string()),
        OpenParen,
        CloseParen,
        OpenBrace,
        Let,
        Ident("a".to_string()),
        Assign,
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

    assert_eq!(&lexer(input).unwrap(), &output);
}

#[test]
fn test_lexer_err_num() {
    let input = "let foo = 1b4";
    assert_eq!(lexer(input), Err(LexError::InvalidNum));
}
