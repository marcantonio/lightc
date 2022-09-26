use std::fmt::Display;

use ast::*;
use common::{Operator, Type};

#[derive(Debug, PartialEq, Clone, Serialize)]
pub struct TypedNode {
    pub kind: Kind<TypedNode>,
    pub ty: Option<Type>,
}

impl TypedNode {
    pub fn new_for(
        start_name: String, start_antn: Type, start_expr: Option<TypedNode>, cond_expr: TypedNode,
        step_expr: TypedNode, body: TypedNode, ty: Option<Type>,
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
            ty,
        }
    }

    pub fn new_let(name: String, antn: Type, init: Option<TypedNode>, ty: Option<Type>) -> Self {
        Self { kind: Kind::Let(Let { name, antn, init: init.map(Box::new) }), ty }
    }

    pub fn new_fn(proto: Prototype, body: Option<TypedNode>, ty: Option<Type>) -> Self {
        Self { kind: Kind::Fn(Fn { proto: Box::new(proto), body: body.map(Box::new) }), ty }
    }

    pub fn new_struct(
        name: String, fields: Vec<TypedNode>, methods: Vec<TypedNode>, ty: Option<Type>,
    ) -> Self {
        Self { kind: Kind::Struct(Struct { name, fields, methods }), ty }
    }

    pub fn new_lit(value: Literal<TypedNode>, ty: Option<Type>) -> Self {
        Self { kind: Kind::Lit(Lit { value }), ty }
    }

    pub fn new_ident(name: String, ty: Option<Type>) -> Self {
        Self { kind: Kind::Ident(Ident { name }), ty }
    }

    pub fn new_binop(op: Operator, lhs: TypedNode, rhs: TypedNode, ty: Option<Type>) -> Self {
        Self { kind: Kind::BinOp(BinOp { op, lhs: Box::new(lhs), rhs: Box::new(rhs) }), ty }
    }

    pub fn new_unop(op: Operator, rhs: TypedNode, ty: Option<Type>) -> Self {
        Self { kind: Kind::UnOp(UnOp { op, rhs: Box::new(rhs) }), ty }
    }

    pub fn new_call(name: String, args: Vec<TypedNode>, ty: Option<Type>) -> Self {
        Self { kind: Kind::Call(Call { name, args }), ty }
    }

    pub fn new_cond(
        cond_expr: TypedNode, then_block: TypedNode, else_block: Option<TypedNode>, ty: Option<Type>,
    ) -> Self {
        Self {
            kind: Kind::Cond(Cond {
                cond_expr: Box::new(cond_expr),
                then_block: Box::new(then_block),
                else_block: else_block.map(Box::new),
            }),
            ty,
        }
    }

    pub fn new_block(list: Vec<TypedNode>, ty: Option<Type>) -> Self {
        Self { kind: Kind::Block(Block { list }), ty }
    }

    pub fn new_index(binding: TypedNode, idx: TypedNode, ty: Option<Type>) -> Self {
        Self { kind: Kind::Index(Index { binding: Box::new(binding), idx: Box::new(idx) }), ty }
    }

    pub fn ty(&self) -> Option<&Type> {
        self.ty.as_ref()
    }
}

impl Node for TypedNode {}

impl Display for TypedNode {
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

#[derive(Debug, PartialEq, Clone, Serialize)]
pub enum Kind<T: Node> {
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
