use serde::Serialize;
use std::iter::Peekable;

use crate::token::{Symbol, Token, TokenType, Type};

type LexResult = std::result::Result<Token, LexError>;

pub(crate) struct Lexer {
    stream: Peekable<StreamIter<char>>,
    pub tokens: Vec<Token>,
}

impl Lexer {
    pub fn new(input: &str) -> Self {
        Lexer {
            stream: StreamIter::new(input).peekable(),
            tokens: vec![],
        }
    }

    // Scan all input
    pub fn scan(mut self) -> Result<Vec<Token>, LexError> {
        loop {
            let token = self.lex()?;
            if token.is_eof() {
                break;
            }
            self.tokens.push(token);
        }
        Ok(self.tokens)
    }

    // Recursively process enough characters to produce one token
    fn lex(&mut self) -> LexResult {
        let cur = match self.stream.next() {
            Some(cur) => cur,
            None => return Ok(Token::default()),
        };

        // Ignore whitespace
        if cur.value.is_ascii_whitespace() {
            while let Some(c) = self.stream.peek() {
                if !c.value.is_ascii_whitespace() {
                    return self.lex();
                }
                self.stream.next();
            }
            return self.lex(); // Eat trailing newline
        }

        // Single line comments
        if cur == '/' && matches!(self.stream.peek(), Some(c) if *c == '/') {
            while let Some(c) = self.stream.next() {
                if c == '\n' {
                    return self.lex();
                }
            }
            return self.lex(); // Eat trailing comment
        }

        // Keywords, types, and identifiers
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
                "fn" => TokenType::Fn,
                "let" => TokenType::Let,
                "for" => TokenType::For,
                "if" => TokenType::If,
                "else" => TokenType::Else,
                "extern" => TokenType::Extern,
                "true" => TokenType::Bool(true),
                "false" => TokenType::Bool(false),
                "int8" => TokenType::VarType(Type::Int8),
                "int16" => TokenType::VarType(Type::Int16),
                "int32" => TokenType::VarType(Type::Int32),
                "int64" => TokenType::VarType(Type::Int64),
                "uint8" => TokenType::VarType(Type::UInt8),
                "uint16" => TokenType::VarType(Type::UInt16),
                "uint32" => TokenType::VarType(Type::UInt32),
                "uint64" => TokenType::VarType(Type::UInt64),
                "float" => TokenType::VarType(Type::Float),
                "double" => TokenType::VarType(Type::Double),
                "bool" => TokenType::VarType(Type::Bool),
                "char" => TokenType::VarType(Type::UInt8),
                // TODO: don't hardcode these
                "int" => TokenType::VarType(Type::Int32),
                "uint" => TokenType::VarType(Type::UInt32),
                _ => TokenType::Ident(identifier),
            };

            return Ok(Token::from((tt, cur)));
        }

        // Literal numbers
        if cur.value.is_ascii_digit() {
            let mut n = String::from(cur.value);
            while let Some(c) = self.stream.peek() {
                if c.value.is_ascii_alphanumeric() || *c == '.' {
                    n.push(c.value);
                    self.stream.next();
                } else {
                    break;
                }
            }

            return Ok(Token::from((TokenType::Num(n), cur)));
        }

        // Multi-character operators
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
                '-' if next == &'>' => {
                    self.stream.next();
                    return Ok(Token::from((TokenType::Op(Symbol::RetType), cur)));
                }
                _ => (),
            }
        }

        // Everything else
        let tt = match cur.value {
            '+' => TokenType::Op(Symbol::Add),
            '-' => TokenType::Op(Symbol::Sub),
            '*' => TokenType::Op(Symbol::Mul),
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

// Provides additional context for each source character
#[derive(Debug, Clone, Copy, PartialEq)]
struct ContextElement<T> {
    value: T,
    line: usize,
    column: usize,
}

impl<T> ContextElement<T> {
    fn new(value: T, line: usize, column: usize) -> Self {
        ContextElement {
            value,
            line: line + 1,
            column: column + 1,
        }
    }
}

impl PartialEq<char> for ContextElement<char> {
    fn eq(&self, other: &char) -> bool {
        self.value == *other
    }
}

impl<T> From<(TokenType, ContextElement<T>)> for Token {
    fn from((ty, ContextElement { line, column, .. }): (TokenType, ContextElement<T>)) -> Self {
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
    type Item = ContextElement<char>;

    fn next(&mut self) -> Option<Self::Item> {
        let line = self.lines.get(self.line)?;
        let cc = line
            .get(self.column)
            .map(|c| ContextElement::new(*c, self.line, self.column))
            .or_else(|| {
                self.line += 1;
                self.column = 0;
                self.lines.get(self.line).and_then(|line| {
                    line.get(self.column)
                        .map(|c| ContextElement::new(*c, self.line, self.column))
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

impl<T> From<(String, ContextElement<T>)> for LexError {
    fn from((msg, cp): (String, ContextElement<T>)) -> Self {
        LexError {
            message: msg,
            line: cp.line,
            column: cp.column,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_lexer() {
        insta::with_settings!({ snapshot_path => "tests/snapshots", prepend_module_to_snapshot => false }, {
            insta::glob!("tests/inputs/lexer/*.input", |path| {
                let input = std::fs::read_to_string(path).unwrap();
                insta::assert_yaml_snapshot!(Lexer::new(&input).scan());
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
        assert_eq!(ContextElement::new('a', 0, 0), stream.next().unwrap());
        assert_eq!(ContextElement::new('b', 0, 1), stream.next().unwrap());
        assert_eq!(ContextElement::new('c', 0, 2), stream.next().unwrap());
        assert_eq!(ContextElement::new('\n', 0, 3), stream.next().unwrap());
        assert_eq!(ContextElement::new('d', 1, 0), stream.next().unwrap());
        assert_eq!(ContextElement::new('e', 1, 1), stream.next().unwrap());
        assert_eq!(ContextElement::new('f', 1, 2), stream.next().unwrap());
        assert_eq!(ContextElement::new('\n', 1, 3), stream.next().unwrap());
        assert_eq!(ContextElement::new('g', 2, 0), stream.next().unwrap());
        assert_eq!(ContextElement::new('h', 2, 1), stream.next().unwrap());
        assert_eq!(ContextElement::new('i', 2, 2), stream.next().unwrap());
        assert_eq!(ContextElement::new('\n', 2, 3), stream.next().unwrap());
        assert_eq!(None, stream.next());
        assert_eq!(None, stream.next());
    }

    #[test]
    fn test_lex() {
        use Symbol::*;
        use TokenType::*;

        let input = "\
foo + bar
// bar
/ not_a_comment
baz
";
        let mut lexer = Lexer::new(input);

        assert_eq!(Ok(Token::new(Ident("foo".to_string()), 1, 1)), lexer.lex());
        assert_eq!(Ok(Token::new(Op(Add), 1, 5)), lexer.lex());
        assert_eq!(Ok(Token::new(Ident("bar".to_string()), 1, 7)), lexer.lex());
        assert_eq!(Ok(Token::new(Op(Div), 3, 1)), lexer.lex());
        assert_eq!(
            Ok(Token::new(Ident("not_a_comment".to_string()), 3, 3)),
            lexer.lex()
        );
        assert_eq!(Ok(Token::new(Ident("baz".to_string()), 4, 1)), lexer.lex());
        assert_eq!(Ok(Token::default()), lexer.lex());
    }
}
