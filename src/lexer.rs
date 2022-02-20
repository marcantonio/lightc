use serde::Serialize;
use std::iter::Peekable;

#[derive(PartialEq, Serialize)]
pub struct Token {
    pub(crate) ty: TokenType,
    line: usize,
    column: usize,
}

impl Token {
    fn new(ty: TokenType, line: usize, column: usize) -> Self {
        Token { ty, line, column }
    }
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.ty)
    }
}

impl std::fmt::Debug for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.ty)
    }
}

#[derive(Debug, PartialEq, Serialize)]
pub enum TokenType {
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
    Int(u64),
    Let,
    Op(Symbol),
    OpenBrace,
    OpenParen,
    Semicolon,
    VarType(Type),
}

impl std::fmt::Display for TokenType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Debug, PartialEq, Clone, Copy, Serialize)]
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

#[derive(Debug, PartialEq, Serialize)]
pub enum Type {
    U64,
}

#[derive(Debug, PartialEq, Serialize)]
pub struct LexError {
    message: String,
    line: usize,
    column: usize,
}

impl std::fmt::Display for LexError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Lexer error: {} at {}:{}",
            self.message, self.line, self.column
        )
    }
}

impl std::error::Error for LexError {}

pub type LexResult = std::result::Result<Token, LexError>;

pub struct Lexer {
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
            None => return Ok(Token::new(TokenType::Eof, 0, 0)),
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
                "u64" => TokenType::VarType(Type::U64),
                "fn" => TokenType::Fn,
                "for" => TokenType::For,
                "if" => TokenType::If,
                "let" => TokenType::Let,
                _ => TokenType::Ident(identifier),
            };

            return Ok(Token::new(tt, cur.line, cur.column));
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
                Ok(n) => Ok(Token::new(TokenType::Int(n), cur.line, cur.column)),
                Err(_) => Err(LexError {
                    message: format!("Invalid number: {}", num),
                    line: cur.line,
                    column: cur.column,
                }),
            };
        }

        // Logical operators
        if let Some(next) = self.stream.peek() {
            match cur.value {
                '=' if next == &'=' => {
                    self.stream.next();
                    return Ok(Token::new(TokenType::Op(Symbol::Eq), cur.line, cur.column));
                }
                '&' if next == &'&' => {
                    self.stream.next();
                    return Ok(Token::new(TokenType::Op(Symbol::And), cur.line, cur.column));
                }
                '|' if next == &'|' => {
                    self.stream.next();
                    return Ok(Token::new(TokenType::Op(Symbol::Or), cur.line, cur.column));
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
                return Err(LexError {
                    message: format!("Unknown character: {}", c),
                    line: cur.line,
                    column: cur.column,
                })
            }
        };

        Ok(Token::new(tt, cur.line, cur.column))
    }
}

impl Iterator for Lexer {
    type Item = LexResult;

    fn next(&mut self) -> Option<Self::Item> {
        match self.lex() {
            Ok(Token {
                ty: TokenType::Eof, ..
            }) => None,
            x => Some(x),
        }
    }
}

#[derive(Debug, PartialEq)]
struct ContextPoint<T> {
    value: T,
    line: usize,
    column: usize,
}

impl<T> ContextPoint<T> {
    pub(crate) fn new(value: T, line: usize, column: usize) -> Self {
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

#[cfg(test)]
mod test {
    use super::*;

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
        assert_eq!(Ok(Token::new(Op(Symbol::Assign), 1, 9)), lexer.lex());
        assert_eq!(Ok(Token::new(Int(14), 1, 11)), lexer.lex());
        assert_eq!(Ok(Token::new(Op(Div), 3, 1)), lexer.lex());
        assert_eq!(
            Ok(Token::new(Ident("not_a_comment".to_string()), 3, 3)),
            lexer.lex()
        );
        assert_eq!(Ok(Token::new(Ident("baz".to_string()), 4, 1)), lexer.lex());
        assert_eq!(Ok(Token::new(Eof, 0, 0)), lexer.lex());
    }

    #[test]
    fn test_lex_error() {
        let input = "1c4";
        let mut lexer = Lexer::new(input);
        assert_eq!(
            "Lexer error: Invalid number: 1c4 at 1:1",
            lexer.lex().unwrap_err().to_string()
        );

        let input = " %";
        let mut lexer = Lexer::new(input);
        assert_eq!(
            String::from("Lexer error: Unknown character: % at 1:2"),
            lexer.lex().unwrap_err().to_string()
        );
    }
}
