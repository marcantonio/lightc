use std::fmt::Display;

use ast::*;
use common::Type;

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
