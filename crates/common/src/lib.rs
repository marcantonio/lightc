use serde::{Deserialize, Serialize};

pub use cli_args::CliArgs;
pub use literal::Literal;
pub use prototype::Prototype;
pub use symbol_table::{Symbol, SymbolTable};

mod cli_args;
pub mod literal;
mod macros;
pub mod prototype;
pub mod symbol_table;

// A Operator is an extra layer of abstraction between TokenType::Op() and the
// actual character. Convenient in Rust to help constrain matching.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Serialize, Deserialize)]
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

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
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
    SArray(Box<Type>, usize),
    Comp(String),
}

impl Type {
    pub fn is_primitive(&self) -> bool {
        !matches!(self, Type::Comp(_) | Type::SArray(_, _))
    }
}

impl From<&str> for Type {
    fn from(ty: &str) -> Self {
        use Type::*;

        if ty.starts_with("sarray") {
            let start = ty.find('(').unwrap_or_else(|| unreachable!("malformed array annotation"));
            let end = ty.find(')').unwrap_or_else(|| unreachable!("malformed array annotation"));
            let (inner, sz) = ty[start + 1..end]
                .split_once(", ")
                .unwrap_or_else(|| unreachable!("malformed array annotation"));
            return SArray(
                Box::new(Type::from(inner)),
                sz.parse().unwrap_or_else(|err| unreachable!("malformed array annotation: {}", err)),
            );
        }

        match ty {
            "int8" => Int8,
            "int16" => Int16,
            "int32" => Int32,
            "int64" => Int64,
            "uint8" => UInt8,
            "uint16" => UInt16,
            "uint32" => UInt32,
            "uint64" => UInt64,
            "float" => Float,
            "double" => Double,
            "bool" => Bool,
            "char" => Char,
            "void" => Void,
            "int" => Int32,
            "uint" => UInt32,
            x => Comp(x.to_owned()),
        }
    }
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
        let s = match self {
            Type::Comp(ty) => ty.to_owned(),
            _ => format!("{:?}", self).to_ascii_lowercase(),
        };
        write!(f, "{}", s)
    }
}

#[cfg(test)]
mod test {
    use crate::Type;

    #[test]
    fn test_type_from() {
        assert_eq!(Type::from("int32"), Type::Int32);
        assert_eq!(Type::from("Int32"), Type::Comp(String::from("Int32")));
        assert_eq!(Type::from("sarray(int, 3)"), Type::SArray(Box::new(Type::Int32), 3));
    }
}
