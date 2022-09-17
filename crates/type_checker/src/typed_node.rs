use std::fmt::Display;

use common::Type;
use parser::ast::*;

#[derive(Debug, PartialEq, Clone, Serialize)]
pub struct TypedNode {
    pub node: NodeKind<TypedNode>,
    pub ty: Option<Type>,
}

impl TypedNode {
    pub fn ty(&self) -> Option<&Type> {
        self.ty.as_ref()
    }
}

#[derive(Debug, PartialEq, Clone, Serialize)]
pub enum NodeKind<T: Node> {
    // Statements
    For(For<T>),
    Let(Let<T>),
    Fn(Fn<T>),
    Struct(Struct<T>),

    // Expressions
    Lit(Lit<T>),
    Ident(Ident),
    BinOp(BinOp<T>),
    UnOp(UnOp<T>),
    Call(Call<T>),
    Cond(Cond<T>),
    Block(Block<T>),
    Index(Index<T>),
}

// XXX move Display into Node
impl Node for TypedNode {}

impl Display for TypedNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use NodeKind::*;
        match &self.node {
            For(s) => write!(f, "{}", s),
            Let(s) => write!(f, "{}", s),
            Fn(s) => write!(f, "{}", s),
            Struct(s) => write!(f, "{}", s),
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
