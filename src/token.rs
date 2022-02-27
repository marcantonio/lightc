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
    pub(crate) fn new(ty: TokenType, line: usize, column: usize) -> Self {
        Token {
            tt: ty,
            line,
            column,
        }
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
pub enum TokenType {
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
    //VarType(Type),
}

impl std::fmt::Display for TokenType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use TokenType::*;

        match self {
            Eof => write!(f, "EOF"),
            Op(s) => write!(f, "{}", s),
            Ident(i) => write!(f, "identifier: {}", i),
            Int(i) => write!(f, "integer: {}", i),
            tt => write!(f, "{:?}", tt),
        }
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

// #[derive(Debug, PartialEq, Clone, Serialize)]
// pub enum Type {
//     U64,
// }
