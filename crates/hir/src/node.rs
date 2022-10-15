use std::fmt::Display;

use ast::Node;
use serde::Serialize;

use common::{Operator, Type};

#[derive(Debug, PartialEq, Clone, Serialize)]
pub struct HirNode {
    pub kind: NodeKind<HirNode>,
}

impl HirNode {
    // XXX: make node type generic in trait???
    pub fn new_for(
        start_name: String, start_antn: Type, start_expr: Option<HirNode>, cond_expr: HirNode,
        step_expr: HirNode, body: HirNode,
    ) -> Self {
        Self {
            kind: NodeKind::For(ast::For {
                start_name,
                start_antn,
                start_expr: start_expr.map(Box::new),
                cond_expr: Box::new(cond_expr),
                step_expr: Box::new(step_expr),
                body: Box::new(body),
            }),
        }
    }

    pub fn new_let(name: String, antn: Type, init: Option<HirNode>) -> Self {
        Self { kind: NodeKind::Let(ast::Let { name, antn, init: init.map(Box::new) }) }
    }

    pub fn new_fn(proto: ast::Prototype, body: Option<HirNode>) -> Self {
        Self { kind: NodeKind::Fn(ast::Fn { proto: Box::new(proto), body: body.map(Box::new) }) }
    }

    pub fn new_lit(value: ast::Literal<HirNode>, ty: Option<Type>) -> Self {
        Self { kind: NodeKind::Lit(ast::Lit { value, ty }) }
    }

    pub fn new_ident(name: String, ty: Option<Type>) -> Self {
        Self { kind: NodeKind::Ident(ast::Ident { name, ty }) }
    }

    pub fn new_binop(op: Operator, lhs: HirNode, rhs: HirNode, ty: Option<Type>) -> Self {
        Self { kind: NodeKind::BinOp(ast::BinOp { op, lhs: Box::new(lhs), rhs: Box::new(rhs), ty }) }
    }

    pub fn new_unop(op: Operator, rhs: HirNode, ty: Option<Type>) -> Self {
        Self { kind: NodeKind::UnOp(ast::UnOp { op, rhs: Box::new(rhs), ty }) }
    }

    pub fn new_call(name: String, args: Vec<HirNode>, ty: Option<Type>) -> Self {
        Self { kind: NodeKind::Call(ast::Call { name, args, ty }) }
    }

    pub fn new_cond(
        cond_expr: HirNode, then_block: HirNode, else_block: Option<HirNode>, ty: Option<Type>,
    ) -> Self {
        Self {
            kind: NodeKind::Cond(ast::Cond {
                cond_expr: Box::new(cond_expr),
                then_block: Box::new(then_block),
                else_block: else_block.map(Box::new),
                ty,
            }),
        }
    }

    pub fn new_block(list: Vec<HirNode>, ty: Option<Type>) -> Self {
        Self { kind: NodeKind::Block(ast::Block { list, ty }) }
    }

    pub fn new_index(binding: HirNode, idx: HirNode, ty: Option<Type>) -> Self {
        Self { kind: NodeKind::Index(ast::Index { binding: Box::new(binding), idx: Box::new(idx), ty }) }
    }

    pub fn ty(&self) -> Option<&Type> {
        use NodeKind::*;

        match &self.kind {
            Lit(e) => e.ty.as_ref(),
            Ident(e) => e.ty.as_ref(),
            BinOp(e) => e.ty.as_ref(),
            UnOp(e) => e.ty.as_ref(),
            Call(e) => e.ty.as_ref(),
            Cond(e) => e.ty.as_ref(),
            Block(e) => e.ty.as_ref(),
            Index(e) => e.ty.as_ref(),
            _ => None,
        }
    }
}

impl Node for HirNode {}

impl Display for HirNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use NodeKind::*;

        match &self.kind {
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

#[derive(Debug, PartialEq, Clone, Serialize)]
pub enum NodeKind<T: Node> {
    // Statements
    For(ast::For<T>),
    Let(ast::Let<T>),
    Fn(ast::Fn<T>),
    Struct(ast::Struct<T>),

    // Expressions
    Lit(ast::Lit<T>),
    Ident(ast::Ident),
    BinOp(ast::BinOp<T>),
    UnOp(ast::UnOp<T>),
    Call(ast::Call<T>),
    Cond(ast::Cond<T>),
    Block(ast::Block<T>),
    Index(ast::Index<T>),
}
