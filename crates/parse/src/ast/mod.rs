use serde::Serialize;

use common::{Literal, Operator, Prototype, Type};
pub use node::Node;

pub mod node;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Ast<T: VisitableNode> {
    nodes: Vec<T>,
}

impl<T: VisitableNode> Ast<T> {
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

    pub fn append(&mut self, mut other: Self) {
        self.nodes.append(&mut other.nodes);
    }
}

impl<T: VisitableNode> Default for Ast<T> {
    fn default() -> Self {
        Self::new()
    }
}

// Immutable visitor interface

pub trait Visitor {
    type AstNode;
    type Result;

    fn visit_node(&mut self, node: Self::AstNode) -> Self::Result;
    fn visit_for(
        &mut self, start_name: String, start_antn: Type, start_expr: Option<Node>, cond_expr: Node,
        step_expr: Node, body: Node,
    ) -> Self::Result;
    fn visit_let(&mut self, name: String, antn: Type, init: Option<Node>) -> Self::Result;
    fn visit_fn(&mut self, proto: Prototype, body: Option<Node>) -> Self::Result;
    fn visit_struct(&mut self, name: String, fields: Vec<Node>, methods: Vec<Node>) -> Self::Result;
    fn visit_lit(&mut self, value: Literal<Node>, ty: Option<Type>) -> Self::Result;
    fn visit_ident(&mut self, name: String, ty: Option<Type>) -> Self::Result;
    fn visit_binop(&mut self, op: Operator, lhs: Node, rhs: Node, ty: Option<Type>) -> Self::Result;
    fn visit_unop(&mut self, op: Operator, rhs: Node, ty: Option<Type>) -> Self::Result;
    fn visit_call(&mut self, name: String, args: Vec<Node>, ty: Option<Type>) -> Self::Result;
    fn visit_cond(
        &mut self, cond_expr: Node, then_block: Node, else_block: Option<Node>, ty: Option<Type>,
    ) -> Self::Result;
    fn visit_block(&mut self, list: Vec<Node>, ty: Option<Type>) -> Self::Result;
    fn visit_index(&mut self, binding: Node, idx: Node, ty: Option<Type>) -> Self::Result;
    fn visit_fselector(&mut self, comp: Node, field: String, ty: Option<Type>) -> Self::Result;
    fn visit_mselector(
        &mut self, comp: Node, name: String, args: Vec<Node>, ty: Option<Type>,
    ) -> Self::Result;
}

pub trait VisitableNode {
    fn accept<V>(self, v: &mut V) -> V::Result
    where
        V: Visitor<AstNode = Self>;
}
