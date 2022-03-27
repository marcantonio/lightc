use serde::Serialize;

use crate::token::{Symbol, Type};

use self::as_expr::AsExpr;

pub mod as_expr;
mod display;

#[derive(Debug, PartialEq, Serialize)]
pub(crate) struct Ast<T> {
    nodes: Vec<T>,
}

impl<T> Ast<T> {
    pub(crate) fn new() -> Self {
        Ast { nodes: vec![] }
    }

    pub(crate) fn add(&mut self, node: T) {
        self.nodes.push(node)
    }

    pub(crate) fn nodes(&self) -> &Vec<T> { // XXX
        &self.nodes
    }

    pub(crate) fn nodes_mut(&mut self) -> &mut Vec<T> {
        &mut self.nodes
    }
}

#[derive(Debug, PartialEq, Serialize)]
pub(crate) enum Node {
    Stmt(Statement),
    Expr(Expression),
}

impl Node {
    pub(crate) fn ty(&self) -> Result<Option<Type>, String> {
        self.as_expr().map(|e| e.ty())
    }
}

#[derive(Debug, PartialEq, Serialize)]
pub(crate) enum Statement {
    Cond {
        cond_expr: Box<Expression>,
        then_block: Vec<Node>,
        else_block: Option<Vec<Node>>,
    },
    For {
        start_name: String,
        start_antn: Type,
        start_expr: Box<Expression>,
        cond_expr: Box<Expression>,
        step_expr: Box<Expression>,
        body: Vec<Node>,
    },
    Let {
        name: String,
        antn: Type,
        init: Option<Box<Node>>,
    },
    Fn {
        proto: Box<Prototype>,
        body: Option<Vec<Node>>,
    },
}

#[derive(Debug, PartialEq, Serialize)]
pub(crate) enum Expression {
    Lit {
        value: Literal,
        ty: Option<Type>,
    },
    Ident {
        name: String,
        ty: Option<Type>,
    },
    BinOp {
        sym: Symbol,
        lhs: Box<Node>,
        rhs: Box<Node>,
        ty: Option<Type>,
    },
    UnOp {
        sym: Symbol,
        rhs: Box<Node>,
        ty: Option<Type>,
    },
    Call {
        name: String,
        args: Vec<Node>,
        ty: Option<Type>,
    },
}

impl Expression {
    pub(crate) fn ty(&self) -> Option<Type> {
        match self {
            Expression::Lit { ty, .. } => *ty,
            Expression::Ident { ty, .. } => *ty,
            Expression::BinOp { ty, .. } => *ty,
            Expression::UnOp { ty, .. } => *ty,
            Expression::Call { ty, .. } => *ty,
        }
    }
}

#[derive(Debug, PartialEq, Serialize)]
pub(crate) enum Literal {
    I64(i64),
    U64(u64),
    F64(f64),
}

#[derive(Debug, PartialEq, Serialize)]
pub(crate) struct Prototype {
    pub(crate) name: String,
    pub(crate) args: Vec<(String, Type)>,
    pub(crate) ret_type: Option<Type>,
}

// Immutable visitor interface

pub(crate) trait AstVisitor {
    type Result;

    fn visit_stmt(&mut self, s: &Statement) -> Self::Result;
    fn visit_expr(&mut self, e: &Expression) -> Self::Result;
}

pub(crate) trait Visitable {
    fn accept<V: AstVisitor>(&self, v: &mut V) -> V::Result;
}

impl Visitable for Node {
    fn accept<V: AstVisitor>(&self, v: &mut V) -> V::Result {
        match self {
            Node::Stmt(s) => v.visit_stmt(s),
            Node::Expr(e) => v.visit_expr(e),
        }
    }
}

impl Visitable for Expression {
    fn accept<V: AstVisitor>(&self, v: &mut V) -> V::Result {
        v.visit_expr(self)
    }
}

impl Visitable for Statement {
    fn accept<V: AstVisitor>(&self, v: &mut V) -> V::Result {
        v.visit_stmt(self)
    }
}

// Mutable visitor interface

pub(crate) trait AstVisitorMut {
    type Result;

    fn visit_stmt(&mut self, s: &mut Statement) -> Self::Result;
    fn visit_expr(&mut self, e: &mut Expression) -> Self::Result;
}

pub(crate) trait VisitableMut {
    fn accept<V: AstVisitorMut>(&mut self, v: &mut V) -> V::Result;
}

impl VisitableMut for Node {
    fn accept<V: AstVisitorMut>(&mut self, v: &mut V) -> V::Result {
        match self {
            Node::Stmt(s) => v.visit_stmt(s),
            Node::Expr(e) => v.visit_expr(e),
        }
    }
}

impl VisitableMut for Expression {
    fn accept<V: AstVisitorMut>(&mut self, v: &mut V) -> V::Result {
        v.visit_expr(self)
    }
}

impl VisitableMut for Statement {
    fn accept<V: AstVisitorMut>(&mut self, v: &mut V) -> V::Result {
        v.visit_stmt(self)
    }
}
