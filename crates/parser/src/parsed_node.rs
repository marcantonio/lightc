use std::fmt::Display;

use ast::*;
use common::{Operator, Type};
use serde::Serialize;

#[derive(Debug, PartialEq, Clone, Serialize)]
pub struct ParsedNode {
    pub kind: Kind<ParsedNode>,
}

impl ParsedNode {
    pub fn new_for(
        start_name: String, start_antn: Type, start_expr: Option<ParsedNode>, cond_expr: ParsedNode,
        step_expr: ParsedNode, body: ParsedNode,
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

    pub fn new_let(name: String, antn: Type, init: Option<ParsedNode>) -> Self {
        Self { kind: Kind::Let(Let { name, antn, init: init.map(Box::new) }) }
    }

    pub fn new_fn(proto: Prototype, body: Option<ParsedNode>) -> Self {
        Self { kind: Kind::Fn(Fn { proto: Box::new(proto), body: body.map(Box::new) }) }
    }

    pub fn new_struct(name: String, fields: Vec<ParsedNode>, methods: Vec<ParsedNode>) -> Self {
        Self { kind: Kind::Struct(Struct { name, fields, methods }) }
    }

    pub fn new_lit(value: Literal<ParsedNode>) -> Self {
        Self { kind: Kind::Lit(Lit { value }) }
    }

    pub fn new_ident(name: String) -> Self {
        Self { kind: Kind::Ident(Ident { name }) }
    }

    pub fn new_binop(op: Operator, lhs: ParsedNode, rhs: ParsedNode) -> Self {
        Self { kind: Kind::BinOp(BinOp { op, lhs: Box::new(lhs), rhs: Box::new(rhs) }) }
    }

    pub fn new_unop(op: Operator, rhs: ParsedNode) -> Self {
        Self { kind: Kind::UnOp(UnOp { op, rhs: Box::new(rhs) }) }
    }

    pub fn new_call(name: String, args: Vec<ParsedNode>) -> Self {
        Self { kind: Kind::Call(Call { name, args }) }
    }

    pub fn new_cond(cond_expr: ParsedNode, then_block: ParsedNode, else_block: Option<ParsedNode>) -> Self {
        Self {
            kind: Kind::Cond(Cond {
                cond_expr: Box::new(cond_expr),
                then_block: Box::new(then_block),
                else_block: else_block.map(Box::new),
            }),
        }
    }

    pub fn new_block(list: Vec<ParsedNode>) -> Self {
        Self { kind: Kind::Block(Block { list }) }
    }

    pub fn new_index(binding: ParsedNode, idx: ParsedNode) -> Self {
        Self { kind: Kind::Index(Index { binding: Box::new(binding), idx: Box::new(idx) }) }
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

impl Node for ParsedNode {}

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

impl Visitable for ParsedNode {
    fn accept<V: AstVisitor<AstNode = Self>>(self, v: &mut V) -> V::Result {
        use Kind::*;

        match self.kind {
            For(s) => v.visit_for(s),
            Let(s) => v.visit_let(s),
            Fn(s) => v.visit_fn(s),
            Struct(s) => v.visit_struct(s),
            Lit(e) => v.visit_lit(e),
            BinOp(e) => v.visit_binop(e),
            UnOp(e) => v.visit_unop(e),
            Ident(e) => v.visit_ident(e),
            Call(e) => v.visit_call(e),
            Cond(e) => v.visit_cond(e),
            Block(e) => v.visit_block(e),
            Index(e) => v.visit_index(e),
        }
    }
}

impl Display for ParsedNode {
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
