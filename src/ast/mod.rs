use serde::Serialize;

use crate::token::{Symbol, Type};

mod display;

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
    Var {
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

#[derive(Debug, PartialEq, Serialize)]
pub(crate) struct Prototype {
    pub(crate) name: String,
    pub(crate) args: Vec<(String, Type)>,
}
