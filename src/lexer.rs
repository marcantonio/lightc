use std::iter::Peekable;
use serde::Serialize;

use crate::token::{Symbol, Token, TokenType};

type LexResult = std::result::Result<Token, LexError>;

pub(crate) struct Lexer {
    stream: Peekable<StreamIter<char>>,
}

impl Lexer {
    pub fn new(input: &str) -> Self {
        Lexer {
            stream: StreamIter::new(input).peekable(),
        }
    }

    fn lex(&mut self) -> LexResult {
        let cur = match self.stream.next() {
            Some(cur) => cur,
            None => return Ok(Token::default()),
        };

        if cur.value.is_ascii_whitespace() {
            while let Some(c) = self.stream.peek() {
                if !c.value.is_ascii_whitespace() {
                    return self.lex();
                }
                self.stream.next();
            }
            return self.lex(); // Eat trailing newline
        }

        // Comments
        if cur == '/' && matches!(self.stream.peek(), Some(c) if *c == '/') {
            while let Some(c) = self.stream.next() {
                if c == '\n' {
                    return self.lex();
                }
            }
            return self.lex(); // Eat trailing comment
        }

        // Identifiers: keywords, function names, and variables
        if cur.value.is_ascii_alphabetic() {
            let mut identifier = String::from(cur.value);
            while let Some(c) = self.stream.peek() {
                if c.value.is_ascii_alphanumeric() || *c == '_' {
                    identifier.push(c.value);
                    self.stream.next();
                } else {
                    break;
                }
            }

            let tt = match identifier.as_str() {
                "else" => TokenType::Else,
                "extern" => TokenType::Extern,
                //"u64" => TokenTypeVarType(TokenTypeU64),
                "fn" => TokenType::Fn,
                "for" => TokenType::For,
                "if" => TokenType::If,
                "let" => TokenType::Let,
                _ => TokenType::Ident(identifier),
            };

            return Ok(Token::from((tt, cur)));
        }

        // Numbers
        if cur.value.is_ascii_digit() {
            let mut num = String::from(cur.value);
            while let Some(c) = self.stream.peek() {
                if c.value.is_ascii_alphanumeric() || *c == '.' {
                    num.push(c.value);
                    self.stream.next();
                } else {
                    break;
                }
            }

            return match num.parse() {
                Ok(n) => Ok(Token::from((TokenType::Int(n), cur))),
                Err(_) => Err(LexError::from((format!("Invalid number: {}", num), cur))),
            };
        }

        // Logical operators
        if let Some(next) = self.stream.peek() {
            match cur.value {
                '=' if next == &'=' => {
                    self.stream.next();
                    return Ok(Token::from((TokenType::Op(Symbol::Eq), cur)));
                }
                '&' if next == &'&' => {
                    self.stream.next();
                    return Ok(Token::from((TokenType::Op(Symbol::And), cur)));
                }
                '|' if next == &'|' => {
                    self.stream.next();
                    return Ok(Token::from((TokenType::Op(Symbol::Or), cur)));
                }
                _ => (),
            }
        }

        // Everything else
        let tt = match cur.value {
            '+' => TokenType::Op(Symbol::Plus),
            '-' => TokenType::Op(Symbol::Minus),
            '*' => TokenType::Op(Symbol::Mult),
            '/' => TokenType::Op(Symbol::Div),
            '^' => TokenType::Op(Symbol::Pow),
            '>' => TokenType::Op(Symbol::Gt),
            '<' => TokenType::Op(Symbol::Lt),
            '!' => TokenType::Op(Symbol::Not),
            '=' => TokenType::Op(Symbol::Assign),
            '}' => TokenType::CloseBrace,
            ')' => TokenType::CloseParen,
            ':' => TokenType::Colon,
            ',' => TokenType::Comma,
            '{' => TokenType::OpenBrace,
            '(' => TokenType::OpenParen,
            ';' => TokenType::Semicolon,
            c => {
                return Err(LexError::from((format!("Unknown character: {}", c), cur)));
            }
        };

        Ok(Token::from((tt, cur)))
    }
}

impl Iterator for Lexer {
    type Item = LexResult;

    fn next(&mut self) -> Option<Self::Item> {
        match self.lex() {
            Ok(Token {
                tt: TokenType::Eof, ..
            }) => None,
            x => Some(x),
        }
    }
}

// Provides additional context for each source character
#[derive(Debug, PartialEq)]
struct ContextPoint<T> {
    value: T,
    line: usize,
    column: usize,
}

impl<T> ContextPoint<T> {
    fn new(value: T, line: usize, column: usize) -> Self {
        ContextPoint {
            value,
            line: line + 1,
            column: column + 1,
        }
    }
}

impl PartialEq<char> for ContextPoint<char> {
    fn eq(&self, other: &char) -> bool {
        self.value == *other
    }
}

impl<T> From<(TokenType, ContextPoint<T>)> for Token {
    fn from((ty, ContextPoint { line, column, .. }): (TokenType, ContextPoint<T>)) -> Self {
        Token {
            tt: ty,
            line,
            column,
        }
    }
}

// Iterator for the source character stream. Supports line and column context.
struct StreamIter<T> {
    lines: Vec<Vec<T>>,
    line: usize,
    column: usize,
}

impl StreamIter<char> {
    fn new(input: &str) -> Self {
        StreamIter {
            lines: input
                .split_inclusive('\n') // can't use .lines() or we lose '\n'
                .map(|l| l.chars().collect())
                .collect(),
            line: 0,
            column: 0,
        }
    }
}

impl Iterator for StreamIter<char> {
    type Item = ContextPoint<char>;

    fn next(&mut self) -> Option<Self::Item> {
        let line = self.lines.get(self.line);
        let cc = line?
            .get(self.column)
            .map(|c| ContextPoint::new(*c, self.line, self.column))
            .or_else(|| {
                self.line += 1;
                self.column = 0;
                self.lines.get(self.line).and_then(|line| {
                    line.get(self.column)
                        .map(|c| ContextPoint::new(*c, self.line, self.column))
                })
            });
        self.column += 1;
        cc
    }
}

#[derive(Debug, PartialEq, Serialize)]
pub(crate) struct LexError {
    message: String,
    line: usize,
    column: usize,
}

impl std::fmt::Display for LexError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Lexing error: {} at {}:{}",
            self.message, self.line, self.column
        )
    }
}

impl std::error::Error for LexError {}

impl<T> From<(String, ContextPoint<T>)> for LexError {
    fn from((msg, cp): (String, ContextPoint<T>)) -> Self {
        LexError {
            message: msg,
            line: cp.line,
            column: cp.column,
        }
    }
}

#[cfg(test)]
mod test {
    use insta::{assert_yaml_snapshot, glob, with_settings};
    use std::fs;

    use super::*;

    #[test]
    fn test_lexer() {
        with_settings!({ snapshot_path => "tests/snapshots", prepend_module_to_snapshot => false }, {
            glob!("tests/inputs/lexer/*.input", |path| {
                let input = fs::read_to_string(path).unwrap();
                assert_yaml_snapshot!(Lexer::new(&input).collect::<Result<Vec<_>, _>>());
            });
        });
    }

    #[test]
    fn test_stream_next() {
        let input = "\
abc
def
ghi
";
        let mut stream = StreamIter::new(input);
        assert_eq!(ContextPoint::new('a', 0, 0), stream.next().unwrap());
        assert_eq!(ContextPoint::new('b', 0, 1), stream.next().unwrap());
        assert_eq!(ContextPoint::new('c', 0, 2), stream.next().unwrap());
        assert_eq!(ContextPoint::new('\n', 0, 3), stream.next().unwrap());
        assert_eq!(ContextPoint::new('d', 1, 0), stream.next().unwrap());
        assert_eq!(ContextPoint::new('e', 1, 1), stream.next().unwrap());
        assert_eq!(ContextPoint::new('f', 1, 2), stream.next().unwrap());
        assert_eq!(ContextPoint::new('\n', 1, 3), stream.next().unwrap());
        assert_eq!(ContextPoint::new('g', 2, 0), stream.next().unwrap());
        assert_eq!(ContextPoint::new('h', 2, 1), stream.next().unwrap());
        assert_eq!(ContextPoint::new('i', 2, 2), stream.next().unwrap());
        assert_eq!(ContextPoint::new('\n', 2, 3), stream.next().unwrap());
        assert_eq!(None, stream.next());
        assert_eq!(None, stream.next());
    }

    #[test]
    fn test_lex() {
        use Symbol::*;
        use TokenType::*;

        let input = "\
let foo = 14
// bar
/ not_a_comment
baz
";
        let mut lexer = Lexer::new(input);
        assert_eq!(Ok(Token::new(Let, 1, 1)), lexer.lex());
        assert_eq!(Ok(Token::new(Ident("foo".to_string()), 1, 5)), lexer.lex());
        assert_eq!(Ok(Token::new(Op(Assign), 1, 9)), lexer.lex());
        assert_eq!(Ok(Token::new(Int(14), 1, 11)), lexer.lex());
        assert_eq!(Ok(Token::new(Op(Div), 3, 1)), lexer.lex());
        assert_eq!(
            Ok(Token::new(Ident("not_a_comment".to_string()), 3, 3)),
            lexer.lex()
        );
        assert_eq!(Ok(Token::new(Ident("baz".to_string()), 4, 1)), lexer.lex());
        assert_eq!(Ok(Token::default()), lexer.lex());
    }
}
