use serde::Serialize;

use common::Operator;

#[derive(PartialEq, Eq, Clone, Serialize)]
pub struct Token {
    pub tt: TokenType,
    pub line: usize,
    pub column: usize,
}

impl Token {
    pub fn new(tt: TokenType, line: usize, column: usize) -> Self {
        Token { tt, line, column }
    }

    pub fn is_eof(&self) -> bool {
        matches!(self, Token { tt: TokenType::Eof, .. })
    }

    // Return true when the semicolon is one we inserted during lexing
    pub fn is_implicit_semi(&self) -> bool {
        matches!(
            self,
            Token {
                tt: TokenType::Semicolon(i),
                ..
            } if *i
        )
    }
}

impl PartialEq<TokenType> for Token {
    fn eq(&self, other: &TokenType) -> bool {
        self.tt == *other
    }
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.tt)
    }
}

impl std::fmt::Debug for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} ({}:{})", self.tt, self.line, self.column)
    }
}

impl Default for Token {
    fn default() -> Self {
        Token { tt: TokenType::Eof, line: 0, column: 0 }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize)]
pub enum TokenType {
    Bool(bool),
    Break,
    Char(String),
    CloseBrace,
    CloseBracket,
    CloseParen,
    Colon,
    Comma,
    Dot,
    Else,
    Eof,
    Extern,
    Fn,
    For,
    Ident(String),
    If,
    Let,
    Loop,
    Module,
    Next,
    Num(String),
    Op(Operator),
    OpenBrace,
    OpenBracket,
    OpenParen,
    Semicolon(bool), // (is implicit?)
    Struct,
    Use,
}

impl std::fmt::Display for TokenType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use TokenType::*;

        match self {
            Eof => write!(f, "EOF"),
            Op(s) => write!(f, "{}", s),
            Ident(i) => write!(f, "{}", i),
            Num(n) => write!(f, "{}", n),
            Dot => write!(f, "."),
            tt => write!(f, "{:?}", tt),
        }
    }
}
