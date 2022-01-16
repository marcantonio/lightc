use std::{iter::Peekable, str::Chars};

#[derive(Debug, PartialEq)]
pub enum Token {
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
    Int(f64),
    VarType(Type),
    Op(char),
    GreaterThan,
    LessThan,
    Extern,
    Eof,
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Debug, PartialEq)]
pub enum Type {
    F64,
}

#[derive(Debug, PartialEq)]
pub enum LexError {
    InvalidNum,
    UnknownLexeme,
}

pub type LexResult = std::result::Result<Token, LexError>;

pub struct Lexer<'a> {
    stream: Peekable<Chars<'a>>,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        Lexer {
            stream: input.chars().peekable(),
        }
    }

    fn lex_one(&mut self) -> LexResult {
        let cur = match self.stream.next() {
            Some(cur) => cur,
            None => return Ok(Token::Eof),
        };

        if cur.is_ascii_whitespace() {
            while let Some(c) = self.stream.peek() {
                if !c.is_ascii_whitespace() {
                    return self.lex_one();
                }
                self.stream.next();
            }
            return self.lex_one(); // Eat trailing newline
        }

        // Comments
        if cur == '/' && self.stream.peek() == Some(&'/') {
            while let Some(c) = self.stream.next() {
                if c == '\n' {
                    return self.lex_one();
                }
            }
            return self.lex_one(); // Eat trailing comment
        }

        // Identifiers: keywords, function names, and variables
        if cur.is_ascii_alphabetic() {
            let mut identifier = String::from(cur);
            while let Some(&c) = self.stream.peek() {
                if c.is_ascii_alphanumeric() {
                    identifier.push(c);
                    self.stream.next();
                } else {
                    break;
                }
            }

            return Ok(match identifier.as_str() {
                "fn" => Token::Fn,
                "let" => Token::Let,
                "f64" => Token::VarType(Type::F64),
                "extern" => Token::Extern,
                _ => Token::Ident(identifier),
            });
        }

        // Numbers
        if cur.is_ascii_digit() {
            let mut num = String::from(cur);
            while let Some(&c) = self.stream.peek() {
                if c.is_ascii_alphanumeric() {
                    num.push(c);
                    self.stream.next();
                } else {
                    break;
                }
            }

            return match num.parse() {
                Ok(n) => Ok(Token::Int(n)),
                Err(_) => Err(LexError::InvalidNum),
            };
        }

        // Everything else
        Ok(match cur {
            '+' | '-' | '*' | '/' | '^' | '>' | '<' => Token::Op(cur),
            '=' => Token::Assign,
            ':' => Token::Colon,
            ',' => Token::Comma,
            '(' => Token::OpenParen,
            ')' => Token::CloseParen,
            '{' => Token::OpenBrace,
            '}' => Token::CloseBrace,
            x => {
                println!("{:?}", x);
                return Err(LexError::UnknownLexeme);
            }
        })
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = LexResult;

    fn next(&mut self) -> Option<Self::Item> {
        match self.lex_one() {
            Ok(Token::Eof) => None,
            x => Some(x),
        }
    }
}

#[test]
fn test_lex_next() {
    let input = "let foo = 14";
    let mut lexer = Lexer::new(input);
    assert_eq!(lexer.lex_one(), Ok(Token::Let));
    assert_eq!(lexer.lex_one(), Ok(Token::Ident("foo".to_string())));
    assert_eq!(lexer.lex_one(), Ok(Token::Assign));
    assert_eq!(lexer.lex_one(), Ok(Token::Int(14.0)));
}
