use std::fmt::Display;

use serde::Serialize;

pub mod prototype;
pub use prototype::Prototype;
pub mod stmt;
pub use stmt::*;
pub mod expr;
pub use expr::*;

#[derive(Debug, PartialEq, Serialize)]
pub struct Ast<T> {
    nodes: Vec<T>,
}

impl<T> Ast<T> {
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

impl<T> Default for Ast<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, PartialEq, Clone, Serialize)]
pub enum Node {
    // Statements
    For(For),
    Let(Let),
    Fn(Fn),
    Struct(Struct),
    // Expressions
    Lit(Lit),
    Ident(Ident),
    BinOp(BinOp),
    UnOp(UnOp),
    Call(Call),
    Cond(Cond),
    Block(Block),
    Index(Index),
    // Stmt(Statement),
    // Expr(Expression),
}

impl Node {
    pub fn new<F, T>(cons: F, inner: T) -> Self
    where
        F: core::ops::Fn(T) -> Self,
    {
        (cons)(inner)
    }
}

impl Display for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Node::*;
        match self {
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

// Immutable visitor interface

pub trait AstVisitor {
    type Result;

    fn visit_for(&mut self, s: For) -> Self::Result;
    fn visit_let(&mut self, s: Let) -> Self::Result;
    fn visit_fn(&mut self, s: Fn) -> Self::Result;
    fn visit_struct(&mut self, s: Struct) -> Self::Result;
    fn visit_lit(&mut self, e: Lit) -> Self::Result;
    fn visit_binop(&mut self, e: BinOp) -> Self::Result;
    fn visit_unop(&mut self, e: UnOp) -> Self::Result;
    fn visit_ident(&mut self, e: Ident) -> Self::Result;
    fn visit_call(&mut self, e: Call) -> Self::Result;
    fn visit_cond(&mut self, e: Cond) -> Self::Result;
    fn visit_block(&mut self, e: Block) -> Self::Result;
    fn visit_index(&mut self, e: Index) -> Self::Result;
}

pub trait Visitable {
    fn accept<V: AstVisitor>(self, v: &mut V) -> V::Result;
}

impl Visitable for Node {
    fn accept<V: AstVisitor>(self, v: &mut V) -> V::Result {
        match self {
            Node::For(s) => v.visit_for(s),
            Node::Let(s) => v.visit_let(s),
            Node::Fn(s) => v.visit_fn(s),
            Node::Struct(s) => v.visit_struct(s),
            Node::Lit(e) => v.visit_lit(e),
            Node::BinOp(e) => v.visit_binop(e),
            Node::UnOp(e) => v.visit_unop(e),
            Node::Ident(e) => v.visit_ident(e),
            Node::Call(e) => v.visit_call(e),
            Node::Cond(e) => v.visit_cond(e),
            Node::Block(e) => v.visit_block(e),
            Node::Index(e) => v.visit_index(e),
        }
    }
}
