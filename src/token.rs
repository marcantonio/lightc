use serde::Serialize;

#[derive(PartialEq, Serialize)]
pub(crate) struct Token {
    pub(crate) tt: TokenType,
    pub(crate) line: usize,
    pub(crate) column: usize,
}

impl Token {
    // I believe the need for pub here, and also the warning, is a rust-analyzer
    // bug
    #[allow(dead_code)]
    pub(crate) fn new(tt: TokenType, line: usize, column: usize) -> Self {
        Token { tt, line, column }
    }
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.tt)
    }
}

impl std::fmt::Debug for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.tt)
    }
}

impl Default for Token {
    fn default() -> Self {
        Token {
            tt: TokenType::Eof,
            line: 0,
            column: 0,
        }
    }
}

#[derive(Debug, PartialEq, Clone, Serialize)]
pub(crate) enum TokenType {
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
    Let,
    Num(String),
    Op(Symbol),
    OpenBrace,
    OpenParen,
    Semicolon,
    VarType(Type),
}

impl std::fmt::Display for TokenType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use TokenType::*;

        match self {
            Eof => write!(f, "EOF"),
            Op(s) => write!(f, "{}", s),
            Ident(i) => write!(f, "identifier: {}", i),
            Num(i) => write!(f, "number: {}", i),
            tt => write!(f, "{:?}", tt),
        }
    }
}

// A Symbol is an extra layer of abstraction between TokenType::Op() and the
// actual character. Convenient in Rust to help constrain matching.
#[derive(Debug, PartialEq, Clone, Copy, Serialize)]
pub(crate) enum Symbol {
    Add,
    And,
    Assign,
    Div,
    Eq,
    Gt,
    Lt,
    Mul,
    Not,
    Or,
    Pow,
    RetType,
    Sub,
}

impl std::fmt::Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Symbol::*;
        let s = match self {
            Add => "+",
            Assign => "=",
            And => "&&",
            Div => "/",
            Eq => "==",
            Gt => ">",
            Lt => "<",
            Mul => "*",
            Not => "!",
            Or => "||",
            Pow => "^",
            Sub => "-",
            RetType => "->",
        };
        write!(f, "{}", s)
    }
}

#[derive(Debug, PartialEq, Clone, Copy, Serialize)]
pub(crate) enum Type {
    Int32,
    Int64,
    UInt32,
    UInt64,
    Float,
    Double,
    Void,
}

impl Default for Type {
    fn default() -> Self {
        Type::Void
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = format!("{:?}", self).to_ascii_lowercase();
        write!(f, "{}", s)
    }
}
