use std::fmt::Display;

use serde::Serialize;

use crate::Node;
use common::Operator;
pub use literal::Literal;

pub mod literal;

#[derive(Debug, PartialEq, Clone, Serialize)]
pub enum Expression {
    Lit(Lit),
    Ident(Ident),
    BinOp(BinOp),
    UnOp(UnOp),
    Call(Call),
    Cond(Cond),
    Block(Block),
    Index(Index),
}

impl Expression {
    pub fn is_num_literal(&self) -> bool {
        use Literal::*;

        matches!(
            self,
            Expression::Lit(Lit {
                value: Int8(_)
                    | Int16(_)
                    | Int32(_)
                    | Int64(_)
                    | UInt8(_)
                    | UInt16(_)
                    | UInt32(_)
                    | UInt64(_)
                    | Float(_)
                    | Double(_),
                ..
            })
        )
    }
}

impl Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Expression::*;

        match self {
            Lit(e) => write!(f, "{}", e),
            BinOp(e) => write!(f, "{}", e),
            UnOp(e) => write!(f, "{}", e),
            Ident(e) => write!(f, "{}", e),
            Call(e) => write!(f, "{}", e),
            Cond(e) => write!(f, "{}", e),
            Block(e) => write!(f, "{}", e),
            Index(e) => write!(f, "{}", e),
        }
    }
}

#[derive(Debug, PartialEq, Clone, Serialize)]
pub struct Lit {
    pub value: Literal,
}

impl Display for Lit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

#[derive(Debug, PartialEq, Clone, Serialize)]
pub struct Ident {
    pub name: String,
}

impl Display for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[derive(Debug, PartialEq, Clone, Serialize)]
pub struct BinOp {
    pub op: Operator,
    pub lhs: Box<Node>,
    pub rhs: Box<Node>,
}

impl Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} {} {})", self.op, self.lhs, self.rhs)
    }
}

#[derive(Debug, PartialEq, Clone, Serialize)]
pub struct UnOp {
    pub op: Operator,
    pub rhs: Box<Node>,
}

impl Display for UnOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} {})", self.op, self.rhs)
    }
}

#[derive(Debug, PartialEq, Clone, Serialize)]
pub struct Call {
    pub name: String,
    pub args: Vec<Node>,
}

impl Display for Call {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = format!("({}", self.name);
        if !self.args.is_empty() {
            for arg in &self.args {
                s += &format!(" {}", arg);
            }
        }
        write!(f, "{})", s)
    }
}

#[derive(Debug, PartialEq, Clone, Serialize)]
pub struct Cond {
    pub cond_expr: Box<Node>,
    pub then_block: Box<Node>,
    pub else_block: Option<Box<Node>>,
}

impl Display for Cond {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = format!("(if {} {}", self.cond_expr, self.then_block);
        if let Some(alt) = &self.else_block {
            s += &format!(" {}", alt);
        }
        write!(f, "{})", s)
    }
}

#[derive(Debug, PartialEq, Clone, Serialize)]
pub struct Block {
    pub list: Vec<Node>,
}

impl Display for Block {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = "'(".to_string();
        s += &self.list.iter().fold(String::new(), |mut acc, n| {
            acc += &format!("{} ", n);
            acc
        });
        write!(f, "{})", s.strip_suffix(' ').unwrap_or("'()"))
    }
}

#[derive(Debug, PartialEq, Clone, Serialize)]
pub struct Index {
    pub binding: Box<Node>,
    pub idx: Box<Node>,
}

impl Display for Index {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}[{}]", self.binding, self.idx)
    }
}
