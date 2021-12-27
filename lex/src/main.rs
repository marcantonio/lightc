use std::fs;

#[derive(Debug, PartialEq)]
enum Token {
    Fn,
    Let,
    OpenParen,
    CloseParen,
    OpenBrace,
    CloseBrace,
    Comma,
    Colon,
    Assign,
    Ident(String),
    Int(i64),
    Type(String),
    Op(char),
}

#[derive(Debug, PartialEq)]
enum LexError {
    InvalidNum,
}

type Result = std::result::Result<Vec<Token>, LexError>;

fn main() {
    let mut tokens: Vec<Token> = vec![];
    let code = fs::read_to_string("/home/mas/Code/light/mm.lt").expect("Error opening file");
    tokens.append(&mut lexer(&code).expect("Error parsing"));

    println!("{:?}", tokens);
}

fn lexer(input: &str) -> Result {
    let mut tokens = vec![];

    // Main loop; one char at a time
    let mut stream: Vec<char> = input.chars().rev().collect();
    while let Some(mut cur) = stream.pop() {
        // Ignore whitespace
        if cur.is_ascii_whitespace() {
            while let Some(c) = stream.pop() {
                if !c.is_ascii_whitespace() {
                    stream.push(c);
                    break;
                }
            }
        }

        // Comments
        if cur == '/' && stream.last() == Some(&'/') {
            while let Some(c) = stream.pop() {
                if c == '\n' {
                    cur = stream.pop().unwrap();
                    break;
                }
            }
        }

        // Identifiers: keywords, function names, and variables
        if cur.is_ascii_alphabetic() {
            let mut identifier = String::from(cur);
            while let Some(c) = stream.pop() {
                if c.is_ascii_alphanumeric() {
                    identifier.push(c);
                } else {
                    stream.push(c);
                    break;
                }
            }

            tokens.push(match identifier.as_str() {
                "fn" => Token::Fn,
                "let" => Token::Let,
                "u64" | "i64" => Token::Type(identifier),
                _ => Token::Ident(identifier),
            })
        }

        // Numbers
        if cur.is_ascii_digit() {
            let mut num = String::from(cur);
            while let Some(c) = stream.pop() {
                if c.is_ascii_alphanumeric() {
                    num.push(c);
                } else {
                    stream.push(c);
                    break;
                }
            }

            tokens.push(match num.parse() {
                Ok(n) => Token::Int(n),
                Err(_) => return Err(LexError::InvalidNum),
            });
        }

        // Everything else
        if cur == '+' || cur == '-' || cur == '*' || cur == '/' {
            tokens.push(Token::Op(cur));
        } else if cur == '=' {
            tokens.push(Token::Assign);
        } else if cur == ':' {
            tokens.push(Token::Colon);
        } else if cur == ',' {
            tokens.push(Token::Comma);
        } else if cur == '(' {
            tokens.push(Token::OpenParen);
        } else if cur == ')' {
            tokens.push(Token::CloseParen);
        } else if cur == '{' {
            tokens.push(Token::OpenBrace);
        } else if cur == '}' {
            tokens.push(Token::CloseBrace);
        }
    }

    Ok(tokens)
}

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

    println!("{}", input);
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
