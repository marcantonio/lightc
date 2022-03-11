use serde::Serialize;

use crate::token::{Symbol, Type};

mod display;

#[derive(Debug, PartialEq, Serialize)]
pub(crate) enum AstNode {
    Expr(Expression),
    Func(Function),
}

#[derive(Debug, PartialEq, Serialize)]
pub(crate) enum Expression {
    I64(u64),
    U64(u64),
    F64(f64),
    Var {
        name: String,
    },
    BinOp {
        sym: Symbol,
        lhs: Box<Expression>,
        rhs: Box<Expression>,
    },
    UnOp {
        sym: Symbol,
        rhs: Box<Expression>,
    },
    Call {
        name: String,
        args: Vec<Expression>,
    },
    Cond {
        cond: Box<Expression>,
        cons: Vec<Expression>,
        alt: Option<Vec<Expression>>,
    },
    For {
        var_name: String,
        start: Box<Expression>,
        cond: Box<Expression>,
        step: Box<Expression>,
        body: Vec<Expression>,
    },
    Let {
        name: String,
        ty: Type,
        init: Option<Box<Expression>>,
    },
}

#[derive(Debug, PartialEq, Serialize)]
pub(crate) struct Prototype {
    pub(crate) name: String,
    pub(crate) args: Vec<(String, Type)>,
}

#[derive(Debug, PartialEq, Serialize)]
pub(crate) struct Function {
    pub(crate) proto: Box<Prototype>,
    pub(crate) body: Option<Vec<Expression>>,
}
