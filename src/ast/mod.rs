use std::ops::Deref;

use serde::Serialize;

use crate::token::{Symbol, Type};

mod display;

#[derive(Debug, PartialEq, Serialize)]
pub(crate) enum Node {
    Stmt(Statement),
    Expr(Expression),
}

impl<'a> From<&'a Node> for &'a Expression {
    fn from(val: &'a Node) -> Self {
        match val {
            Node::Stmt(_) => todo!(),
            Node::Expr(e) => e,
        }
    }
}

impl From<Node> for Expression {
    fn from(val: Node) -> Self {
        match val {
            Node::Stmt(_) => todo!(),
            Node::Expr(e) => e,
        }
    }
}

fn foo() {
    let n = &Node::Expr(Expression::I64(1));
    let _e: &Expression = n.into();
}

// fn bar(v: Vec<Node>) -> Vec<Expression> {
//     v.into()
// }

// impl Node {
//     pub(crate) fn as_expr(&self) -> &Expression {
//         match self {
//             Node::Stmt(_) => panic!("Expecting wrapped expression"),
//             Node::Expr(e) => e,
//         }
//     }
// }

impl Deref for Node {
    type Target = Expression;

    fn deref(&self) -> &Self::Target {
        self.into()
    }
}

pub(crate) trait AsExpr {
    fn as_expr(&self) -> Vec<&Expression>;
}

pub(crate) trait AsExprOption {
    fn as_expr(&self) -> Option<Vec<&Expression>>;
}

impl AsExpr for Vec<Node> {
    fn as_expr(&self) -> Vec<&Expression> {
        self.iter().map(|n| n.into()).collect()
    }
}

impl AsExprOption for Option<Vec<Node>> {
    fn as_expr(&self) -> Option<Vec<&Expression>> {
        self.as_ref().map(|v| v.as_expr())
    }
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
    }
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
