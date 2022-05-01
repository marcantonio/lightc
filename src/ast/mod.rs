use serde::Serialize;

use self::conversion::AsExpr;
use crate::token::{Symbol, Type};

pub mod conversion;
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

    pub(crate) fn nodes(&self) -> &[T] {
        &self.nodes
    }

    pub(crate) fn nodes_mut(&mut self) -> &mut [T] {
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
    For {
        start_name: String,
        start_antn: Type,
        start_expr: Box<Expression>,
        cond_expr: Box<Expression>,
        step_expr: Box<Expression>,
        body: Box<Expression>,
    },
    Let {
        name: String,
        antn: Type,
        init: Option<Box<Node>>,
    },
    Fn {
        proto: Box<Prototype>,
        body: Option<Box<Expression>>,
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
    Cond {
        cond_expr: Box<Expression>,
        then_block: Box<Expression>,
        else_block: Option<Box<Expression>>,
        ty: Option<Type>,
    },
    Block {
        list: Vec<Node>,
        ty: Option<Type>,
    },
}

impl Expression {
    pub(crate) fn ty(&self) -> Option<Type> {
        use Expression::*;

        match self {
            Lit { ty, .. } => *ty,
            Ident { ty, .. } => *ty,
            BinOp { ty, .. } => *ty,
            UnOp { ty, .. } => *ty,
            Call { ty, .. } => *ty,
            Cond { ty, .. } => *ty,
            Block { ty, .. } => *ty,
        }
    }

    pub(crate) fn is_num_literal(&self) -> bool {
        matches!(
            self,
            Expression::Lit {
                value: Literal::Int8(_)
                    | Literal::Int16(_)
                    | Literal::Int32(_)
                    | Literal::Int64(_)
                    | Literal::UInt8(_)
                    | Literal::UInt16(_)
                    | Literal::UInt32(_)
                    | Literal::UInt64(_)
                    | Literal::Float(_)
                    | Literal::Double(_),
                ..
            }
        )
    }
}

#[derive(Debug, PartialEq, Serialize)]
pub(crate) enum Literal {
    Int8(i8),
    Int16(i16),
    Int32(i32),
    Int64(i64),
    UInt8(u8),
    UInt16(u16),
    UInt32(u32),
    UInt64(u64),
    Float(f32),
    Double(f64),
    Bool(bool),
}

#[derive(Debug, PartialEq, Serialize)]
pub(crate) struct Prototype {
    pub(crate) name: String,
    pub(crate) args: Vec<(String, Type)>,
    pub(crate) ret_ty: Option<Type>,
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
