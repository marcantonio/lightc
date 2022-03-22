use serde::Serialize;

use crate::token::{Symbol, Type};

mod display;

#[derive(Debug, PartialEq, Serialize)]
pub(crate) struct Ast<T: Visitable> {
    nodes: Vec<T>,
}

impl<T: Visitable> Ast<T> {
    pub(crate) fn new() -> Self {
        Ast { nodes: vec![] }
    }

    pub(crate) fn add(&mut self, node: T) {
        self.nodes.push(node)
    }

    pub(crate) fn nodes(&self) -> &Vec<T> {
        &self.nodes
    }
}

#[derive(Debug, PartialEq, Serialize)]
pub(crate) enum Node {
    Stmt(Statement),
    Expr(Expression),
}

#[derive(Debug, PartialEq, Serialize)]
pub(crate) enum Statement {
    Cond {
        cond: Box<Node>,
        cons: Vec<Node>,
        alt: Option<Vec<Node>>,
    },
    For {
        var_name: String,
        start: Box<Node>,
        cond: Box<Node>,
        step: Box<Node>,
        body: Vec<Node>,
    },
    Let {
        name: String,
        ty: Type,
        init: Option<Box<Node>>,
    },
    Fn {
        proto: Box<Prototype>,
        body: Option<Vec<Node>>,
    },
}

#[derive(Debug, PartialEq, Serialize)]
pub(crate) enum Expression {
    I64(u64),
    U64(u64),
    F64(f64),
    Ident {
        name: String,
    },
    BinOp {
        sym: Symbol,
        lhs: Box<Node>,
        rhs: Box<Node>,
    },
    UnOp {
        sym: Symbol,
        rhs: Box<Node>,
    },
    Call {
        name: String,
        args: Vec<Node>,
    },
}

impl Expression {
    pub(crate) fn is_type(&self, ty: Type) -> bool {
        matches!(
            (self, ty),
            (Expression::U64(_), Type::U64)
                | (Expression::I64(_), Type::I64)
                | (Expression::F64(_), Type::F64)
        )
    }

    pub(crate) fn as_type(&self) -> Type {
        match self {
            Expression::I64(_) => Type::I64,
            Expression::U64(_) => Type::U64,
            Expression::F64(_) => Type::F64,
            _ => todo!(),
        }
    }
}

#[derive(Debug, PartialEq, Serialize)]
pub(crate) struct Prototype {
    pub(crate) name: String,
    pub(crate) args: Vec<(String, Type)>,
    pub(crate) ret_type: Option<Type>,
}

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
