use serde::Serialize;

mod macros;
pub mod symbol_table;

#[derive(PartialEq, Clone, Serialize)]
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
        matches!(
            self,
            Token {
                tt: TokenType::Eof,
                ..
            }
        )
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
        Token {
            tt: TokenType::Eof,
            line: 0,
            column: 0,
        }
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
    OpenBracket,
    OpenParen,
    Semicolon(bool), // implicit
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
pub enum Symbol {
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

macro_rules! gen_type_enums {
    ($e1:ident: [$($v1:ident),*], $e2:ident: [$($v2:ident),*]) => {
        #[derive(Debug, PartialEq, Clone, Copy, Serialize)]
        pub enum $e1 {
            $(
                $v1,
            )*
        }

        #[derive(Debug, PartialEq, Clone, Copy, Serialize)]
        pub enum $e2 {
            $(
                $v1,
            )*
            $(
                $v2(PrimativeType),
            )*
        }
    };
}

gen_type_enums!(PrimativeType: [Int8, Int16, Int32, Int64, UInt8, UInt16, UInt32, UInt64, Float, Double, Bool, Char, Void],
                Type: [Array]);

impl Type {
    pub fn as_primative(self) -> PrimativeType {
        match self {
            Type::Int8 => PrimativeType::Int8,
            Type::Int16 => PrimativeType::Int16,
            Type::Int32 => PrimativeType::Int32,
            Type::Int64 => PrimativeType::Int64,
            Type::UInt8 => PrimativeType::UInt8,
            Type::UInt16 => PrimativeType::UInt16,
            Type::UInt32 => PrimativeType::UInt32,
            Type::UInt64 => PrimativeType::UInt64,
            Type::Float => PrimativeType::Float,
            Type::Double => PrimativeType::Double,
            Type::Bool => PrimativeType::Bool,
            Type::Char => PrimativeType::Char,
            Type::Void => PrimativeType::Void,
            Type::Array(_) => unimplemented!("Array is not a primative type"),
        }
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = format!("{:?}", self).to_ascii_lowercase();
        write!(f, "{}", s)
    }
}
