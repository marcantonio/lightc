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
    type Node: Node;
    type Result;

    fn visit_node(&mut self, node: Self::Node) -> Self::Result;
    fn visit_for(&mut self, stmt: For<Self::Node>) -> Self::Result;
    fn visit_let(&mut self, stmt: Let<Self::Node>) -> Self::Result;
    fn visit_fn(&mut self, stmt: Fn<Self::Node>) -> Self::Result;
    fn visit_struct(&mut self, stmt: Struct<Self::Node>) -> Self::Result;
    fn visit_lit(&mut self, expr: Lit<Self::Node>) -> Self::Result;
    fn visit_ident(&mut self, expr: Ident) -> Self::Result;
    fn visit_binop(&mut self, expr: BinOp<Self::Node>) -> Self::Result;
    fn visit_unop(&mut self, expr: UnOp<Self::Node>) -> Self::Result;
    fn visit_call(&mut self, expr: Call<Self::Node>) -> Self::Result;
    fn visit_cond(&mut self, expr: Cond<Self::Node>) -> Self::Result;
    fn visit_block(&mut self, expr: Block<Self::Node>) -> Self::Result;
    fn visit_index(&mut self, expr: Index<Self::Node>) -> Self::Result;
}

pub trait Visitable {
    fn accept<V>(self, v: &mut V) -> V::Result
    where
        V: AstVisitor<Node = Self>;
}

pub trait Node {}
