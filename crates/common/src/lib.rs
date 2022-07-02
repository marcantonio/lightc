use serde::Serialize;

mod macros;
pub mod symbol_cache;
pub use symbol_cache::SymbolCache;
pub mod symbol_table;

#[derive(PartialEq, Clone, Serialize)]
pub struct Token {
    pub tt: TokenType,
    pub line: usize,
    pub column: usize,
}

// XXX: Token in lexer crate?
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

#[derive(Debug, PartialEq, Clone, Serialize)]
pub enum TokenType {
    Bool(bool),
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
    Num(String),
    Op(Operator),
    OpenBrace,
    OpenBracket,
    OpenParen,
    Semicolon(bool), // implicit
    SelfTt,
    Struct,
    VarType(Type),
}

impl std::fmt::Display for TokenType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use TokenType::*;

        match self {
            Eof => write!(f, "EOF"),
            Op(s) => write!(f, "{}", s),
            Ident(i) => write!(f, "{}", i),
            Num(n) => write!(f, "{}", n),
            SelfTt => write!(f, "self"),
            Dot => write!(f, "."),
            tt => write!(f, "{:?}", tt),
        }
    }
}

// A Symbol is an extra layer of abstraction between TokenType::Op() and the
// actual character. Convenient in Rust to help constrain matching.
#[derive(Debug, PartialEq, Clone, Copy, Serialize)]
pub enum Operator {
    Add,
    AddEq,
    And,
    Assign,
    BitAnd,
    BitOr,
    BitXor,
    Dec,
    Div,
    DivEq,
    Eq,
    Gt,
    GtEq,
    Inc,
    Lt,
    LtEq,
    Mul,
    MulEq,
    Not,
    NotEq,
    Or,
    Pow,
    RetType,
    Sub,
    SubEq,
}

impl std::fmt::Display for Operator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Operator::*;
        let s = match self {
            Add => "+",
            AddEq => "+=",
            Assign => "=",
            And => "&&",
            BitAnd => "&",
            BitOr => "|",
            BitXor => "^",
            Dec => "--",
            Div => "/",
            DivEq => "/=",
            Eq => "==",
            Gt => ">",
            GtEq => ">=",
            Inc => "++",
            Lt => "<",
            LtEq => "<=",
            Mul => "*",
            MulEq => "*=",
            Not => "!",
            NotEq => "!=",
            Or => "||",
            Pow => "**",
            RetType => "->",
            Sub => "-",
            SubEq => "-=",
        };
        write!(f, "{}", s)
    }
}

#[derive(Debug, PartialEq, Clone, Serialize)]
pub enum Type {
    Int8,
    Int16,
    Int32,
    Int64,
    UInt8,
    UInt16,
    UInt32,
    UInt64,
    Float,
    Double,
    Bool,
    Char,
    Void,
    Array(Box<Type>, u32),
}

impl Default for Type {
    fn default() -> Self {
        Self::Void
    }
}

impl Default for &Type {
    fn default() -> Self {
        &Type::Void
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = format!("{:?}", self).to_ascii_lowercase();
        write!(f, "{}", s)
    }
}
