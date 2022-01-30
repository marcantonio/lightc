use std::{iter::Peekable, str::Chars};

#[derive(Debug, PartialEq)]
pub enum Token {
    Assign,
    CloseBrace,
    CloseParen,
    Colon,
    Comma,
    Else,
    Eof,
    Extern,
    Fn,
    For,
    Ident(String),
    If,
    Int(f64),
    Let,
    Op(Symbol),
    OpenBrace,
    OpenParen,
    Semicolon,
    VarType(Type),
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Symbol {
    And,
    Assign,
    Div,
    Eq,
    Gt,
    Lt,
    Minus,
    Mult,
    Not,
    Or,
    Plus,
    Pow,
}

impl std::fmt::Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Symbol::Assign => "=",
            Symbol::And => "&&",
            Symbol::Div => "/",
            Symbol::Eq => "==",
            Symbol::Gt => ">",
            Symbol::Lt => "<",
            Symbol::Minus => "-",
            Symbol::Mult => "*",
            Symbol::Not => "!",
            Symbol::Or => "||",
            Symbol::Plus => "+",
            Symbol::Pow => "^",
        };
        write!(f, "{}", s)
    }
}

#[derive(Debug, PartialEq)]
pub enum Type {
    F64,
}

#[derive(Debug, PartialEq)]
pub enum LexError {
    InvalidNum,
    UnknownChar,
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
                if c.is_ascii_alphanumeric() || c == '_' {
                    identifier.push(c);
                    self.stream.next();
                } else {
                    break;
                }
            }

            return Ok(match identifier.as_str() {
                "else" => Token::Else,
                "extern" => Token::Extern,
                "f64" => Token::VarType(Type::F64),
                "fn" => Token::Fn,
                "for" => Token::For,
                "if" => Token::If,
                "let" => Token::Let,
                _ => Token::Ident(identifier),
            });
        }

        // Numbers
        if cur.is_ascii_digit() {
            let mut num = String::from(cur);
            while let Some(&c) = self.stream.peek() {
                if c.is_ascii_alphanumeric() || c == '.' {
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

        // Logical operators
        if let Some(next) = self.stream.peek() {
            match cur {
                '=' if next == &'=' => {
                    self.stream.next();
                    return Ok(Token::Op(Symbol::Eq));
                }
                '&' if next == &'&' => {
                    self.stream.next();
                    return Ok(Token::Op(Symbol::And));
                }
                '|' if next == &'|' => {
                    self.stream.next();
                    return Ok(Token::Op(Symbol::Or));
                }
                _ => ()
            }
        }

        // Everything else
        Ok(match cur {
            '+' => Token::Op(Symbol::Plus),
            '-' => Token::Op(Symbol::Minus),
            '*' => Token::Op(Symbol::Mult),
            '/' => Token::Op(Symbol::Div),
            '^' => Token::Op(Symbol::Pow),
            '>' => Token::Op(Symbol::Gt),
            '<' => Token::Op(Symbol::Lt),
            '!' => Token::Op(Symbol::Not),
            '=' => Token::Op(Symbol::Assign),
            '}' => Token::CloseBrace,
            ')' => Token::CloseParen,
            ':' => Token::Colon,
            ',' => Token::Comma,
            '{' => Token::OpenBrace,
            '(' => Token::OpenParen,
            ';' => Token::Semicolon,
            _ => return Err(LexError::UnknownChar),
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
    assert_eq!(lexer.lex_one(), Ok(Token::Op(Symbol::Assign)));
    assert_eq!(lexer.lex_one(), Ok(Token::Int(14.0)));
}
