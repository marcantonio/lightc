use std::fmt::Display;

use serde::Serialize;

use crate::*;
use common::{Operator, Type};

#[derive(Debug, PartialEq, Clone, Serialize)]
pub struct AstNode {
    pub kind: Kind<AstNode>,
}

impl AstNode {
    pub fn new_for(
        start_name: String, start_antn: Type, start_expr: Option<AstNode>, cond_expr: AstNode,
        step_expr: AstNode, body: AstNode,
    ) -> Self {
        Self {
            kind: Kind::For(For {
                start_name,
                start_antn,
                start_expr: start_expr.map(Box::new),
                cond_expr: Box::new(cond_expr),
                step_expr: Box::new(step_expr),
                body: Box::new(body),
            }),
        }
    }

    pub fn new_let(name: String, antn: Type, init: Option<AstNode>) -> Self {
        Self { kind: Kind::Let(Let { name, antn, init: init.map(Box::new) }) }
    }

    pub fn new_fn(proto: Prototype, body: Option<AstNode>) -> Self {
        Self { kind: Kind::Fn(Fn { proto: Box::new(proto), body: body.map(Box::new) }) }
    }

    pub fn new_struct(name: String, fields: Vec<AstNode>, methods: Vec<AstNode>) -> Self {
        Self { kind: Kind::Struct(Struct { name, fields, methods }) }
    }

    pub fn new_lit(value: Literal<AstNode>, ty: Option<Type>) -> Self {
        Self { kind: Kind::Lit(Lit { value, ty }) }
    }

    pub fn new_ident(name: String, ty: Option<Type>) -> Self {
        Self { kind: Kind::Ident(Ident { name, ty }) }
    }

    pub fn new_binop(op: Operator, lhs: AstNode, rhs: AstNode, ty: Option<Type>) -> Self {
        Self { kind: Kind::BinOp(BinOp { op, lhs: Box::new(lhs), rhs: Box::new(rhs), ty }) }
    }

    pub fn new_unop(op: Operator, rhs: AstNode, ty: Option<Type>) -> Self {
        Self { kind: Kind::UnOp(UnOp { op, rhs: Box::new(rhs), ty }) }
    }

    pub fn new_call(name: String, args: Vec<AstNode>, ty: Option<Type>) -> Self {
        Self { kind: Kind::Call(Call { name, args, ty }) }
    }

    pub fn new_cond(
        cond_expr: AstNode, then_block: AstNode, else_block: Option<AstNode>, ty: Option<Type>,
    ) -> Self {
        Self {
            kind: Kind::Cond(Cond {
                cond_expr: Box::new(cond_expr),
                then_block: Box::new(then_block),
                else_block: else_block.map(Box::new),
                ty,
            }),
        }
    }

    pub fn new_block(list: Vec<AstNode>, ty: Option<Type>) -> Self {
        Self { kind: Kind::Block(Block { list, ty }) }
    }

    pub fn new_index(binding: AstNode, idx: AstNode, ty: Option<Type>) -> Self {
        Self { kind: Kind::Index(Index { binding: Box::new(binding), idx: Box::new(idx), ty }) }
    }

    pub fn ty(&self) -> Option<&Type> {
        use Kind::*;

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

    pub fn is_num_literal(&self) -> bool {
        use Literal::*;

        matches!(
            self.kind,
            Kind::Lit(Lit {
                value: Int8(_)
                    | Int16(_)
                    | Int32(_)
                    | Int64(_)
                    | UInt8(_)
                    | UInt16(_)
                    | UInt32(_)
                    | UInt64(_)
                    | Float(_)
                    | Double(_),
                ..
            })
        )
    }
}

impl VisitableNode for AstNode {}

#[derive(Debug, PartialEq, Clone, Serialize)]
pub enum Kind<T: VisitableNode> {
    // Statements
    For(For<T>),
    Let(Let<T>),
    Fn(Fn<T>),
    Struct(Struct<T>),

    // Expressions
    Lit(Lit<T>),
    Ident(Ident),
    BinOp(BinOp<T>),
    UnOp(UnOp<T>),
    Call(Call<T>),
    Cond(Cond<T>),
    Block(Block<T>),
    Index(Index<T>),
}

impl Visitable for AstNode {
    fn accept<V: AstVisitor<Node = Self>>(self, v: &mut V) -> V::Result {
        use Kind::*;

        match self.kind {
            For(s) => v.visit_for(s),
            Let(s) => v.visit_let(s),
            Fn(s) => v.visit_fn(s),
            Struct(s) => v.visit_struct(s),
            Lit(e) => v.visit_lit(e),
            Ident(e) => v.visit_ident(e),
            BinOp(e) => v.visit_binop(e),
            UnOp(e) => v.visit_unop(e),
            Call(e) => v.visit_call(e),
            Cond(e) => v.visit_cond(e),
            Block(e) => v.visit_block(e),
            Index(e) => v.visit_index(e),
        }
    }
}

impl Display for AstNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Kind::*;

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
