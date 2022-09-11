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
    Stmt(Statement),
    Expr(Expression),
}

impl Node {
    pub fn new<F, T>(cons: F, inner: T) -> Self
    where
        F: core::ops::Fn(T) -> Self,
    {
        (cons)(inner)
    }

    pub fn as_stmt(&self) -> &Statement {
        match self {
            Node::Stmt(s) => s,
            Node::Expr(_) => unreachable!("expected Statement"),
        }
    }

    pub fn to_expr(self) -> Expression {
        match self {
            Node::Stmt(_) => unreachable!("expected Expression"),
            Node::Expr(e) => e,
        }
    }

    pub fn as_expr(&self) -> &Expression {
        match self {
            Node::Stmt(_) => unreachable!("expected Expression"),
            Node::Expr(e) => e,
        }
    }

    pub fn as_expr_mut(&mut self) -> &mut Expression {
        match self {
            Node::Stmt(_) => unreachable!("expected Expression"),
            Node::Expr(e) => e,
        }
    }
}

impl Display for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Node::Stmt(stmt) => write!(f, "{}", stmt),
            Node::Expr(expr) => write!(f, "{}", expr),
        }
    }
}

// Immutable visitor interface

pub trait AstVisitor {
    type Result;

    fn visit_stmt(&mut self, s: Statement) -> Self::Result;
    fn visit_expr(&mut self, e: Expression) -> Self::Result;
}

pub trait Visitable {
    fn accept<V: AstVisitor>(self, v: &mut V) -> V::Result;
}

impl Visitable for Node {
    fn accept<V: AstVisitor>(self, v: &mut V) -> V::Result {
        match self {
            Node::Stmt(s) => v.visit_stmt(s),
            Node::Expr(e) => v.visit_expr(e),
        }
    }
}

impl Visitable for Statement {
    fn accept<V: AstVisitor>(self, v: &mut V) -> V::Result {
        v.visit_stmt(self)
    }
}

impl Visitable for Expression {
    fn accept<V: AstVisitor>(self, v: &mut V) -> V::Result {
        v.visit_expr(self)
    }
}
