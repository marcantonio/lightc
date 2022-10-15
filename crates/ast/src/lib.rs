use serde::Serialize;

pub use expr::*;
pub use node::{AstNode, NodeKind};
pub use prototype::Prototype;
pub use stmt::*;

mod expr;
mod node;
mod prototype;
mod stmt;

#[derive(Debug, PartialEq, Serialize)]
pub struct Ast<T: Node> {
    nodes: Vec<T>,
}

impl<T: Node> Ast<T> {
    pub fn new() -> Self {
        Ast { nodes: vec![] }
    }

    pub fn add(&mut self, node: T) {
        self.nodes.push(node)
    }

    pub fn nodes(&self) -> &[T] {
        &self.nodes
    }

    pub fn into_nodes(self) -> Vec<T> {
        self.nodes
    }
}

impl<T: Node> Default for Ast<T> {
    fn default() -> Self {
        Self::new()
    }
}

// Immutable visitor interface

pub trait AstVisitor {
    type AstNode: Node;
    type Result;

    fn visit_for(&mut self, s: For<Self::AstNode>) -> Self::Result;
    fn visit_let(&mut self, s: Let<Self::AstNode>) -> Self::Result;
    fn visit_fn(&mut self, s: Fn<Self::AstNode>) -> Self::Result;
    fn visit_struct(&mut self, s: Struct<Self::AstNode>) -> Self::Result;
    fn visit_lit(&mut self, e: Lit<Self::AstNode>) -> Self::Result;
    fn visit_binop(&mut self, e: BinOp<Self::AstNode>) -> Self::Result;
    fn visit_unop(&mut self, e: UnOp<Self::AstNode>) -> Self::Result;
    fn visit_ident(&mut self, e: Ident) -> Self::Result;
    fn visit_call(&mut self, e: Call<Self::AstNode>) -> Self::Result;
    fn visit_cond(&mut self, e: Cond<Self::AstNode>) -> Self::Result;
    fn visit_block(&mut self, e: Block<Self::AstNode>) -> Self::Result;
    fn visit_index(&mut self, e: Index<Self::AstNode>) -> Self::Result;
}

pub trait Visitable {
    fn accept<V>(self, v: &mut V) -> V::Result
    where
        V: AstVisitor<AstNode = Self>;
}

pub trait Node {}
