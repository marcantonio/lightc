use std::fmt::Display;

use serde::Serialize;

use super::Node;
use common::{Operator, Type};
pub use literal::Literal;
pub mod literal;

#[derive(Debug, PartialEq, Clone, Serialize)]
pub struct Lit<T: Node> {
    pub value: Literal<T>,
    pub ty: Option<Type>,
}

impl<T> Display for Lit<T>
where
    T: Node + Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

#[derive(Debug, PartialEq, Clone, Serialize)]
pub struct Ident {
    pub name: String,
    pub ty: Option<Type>,
}

impl Display for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[derive(Debug, PartialEq, Clone, Serialize)]
pub struct BinOp<T: Node> {
    pub op: Operator,
    pub lhs: Box<T>,
    pub rhs: Box<T>,
    pub ty: Option<Type>,
}

impl<T> Display for BinOp<T>
where
    T: Node + Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} {} {})", self.op, self.lhs, self.rhs)
    }
}

#[derive(Debug, PartialEq, Clone, Serialize)]
pub struct UnOp<T: Node> {
    pub op: Operator,
    pub rhs: Box<T>,
    pub ty: Option<Type>,
}

impl<T> Display for UnOp<T>
where
    T: Node + Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} {})", self.op, self.rhs)
    }
}

#[derive(Debug, PartialEq, Clone, Serialize)]
pub struct Call<T: Node> {
    pub name: String,
    pub args: Vec<T>,
    pub ty: Option<Type>,
}

impl<T> Display for Call<T>
where
    T: Node + Display,
{
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
pub struct Cond<T: Node> {
    pub cond_expr: Box<T>,
    pub then_block: Box<T>,
    pub else_block: Option<Box<T>>,
    pub ty: Option<Type>,
}

impl<T> Display for Cond<T>
where
    T: Node + Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = format!("(if {} {}", self.cond_expr, self.then_block);
        if let Some(alt) = &self.else_block {
            s += &format!(" {}", alt);
        }
        write!(f, "{})", s)
    }
}

#[derive(Debug, PartialEq, Clone, Serialize)]
pub struct Block<T: Node> {
    pub list: Vec<T>,
    pub ty: Option<Type>,
}

impl<T> Display for Block<T>
where
    T: Node + Display,
{
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
pub struct Index<T: Node> {
    pub binding: Box<T>,
    pub idx: Box<T>,
    pub ty: Option<Type>,
}

impl<T> Display for Index<T>
where
    T: Node + Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}[{}]", self.binding, self.idx)
    }
}
