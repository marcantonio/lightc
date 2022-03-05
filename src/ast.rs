use serde::Serialize;
use std::fmt::Display;

use crate::token::{Symbol, Type};

#[derive(Debug, PartialEq, Serialize)]
pub(crate) enum AstNode {
    Expr(Expression),
    Func(Function),
}

impl Display for AstNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AstNode::Expr(expr) => write!(f, "{}", expr),
            AstNode::Func(func) => write!(f, "{}", func),
        }
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

impl Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Expression::*;
        match self {
            U64(v) => write!(f, "{}", v),
            I64(v) => write!(f, "{}", v),
            F64(v) => write!(f, "{}", v),
            BinOp { sym, lhs, rhs } => write!(f, "({} {} {})", sym, lhs, rhs),
            UnOp { sym, rhs } => write!(f, "({} {})", sym, rhs),
            Var { name } => write!(f, "{}", name),
            Call { name, args } => {
                let mut s = format!("({}", name);
                if !args.is_empty() {
                    for arg in args {
                        s += &format!(" {}", arg);
                    }
                }
                write!(f, "{})", s)
            }
            Cond { cond, cons, alt } => {
                let mut s = format!("(if {}", cond);
                s += &cons.iter().fold(String::new(), |mut acc, n| {
                    acc += &format!(" {}", n);
                    acc
                });

                if let Some(alt) = alt {
                    s += &alt.iter().fold(String::new(), |mut acc, n| {
                        acc += &format!(" {}", n);
                        acc
                    });
                }
                write!(f, "{})", s)
            }
            For {
                var_name,
                start,
                cond,
                step,
                body,
            } => {
                let mut s = format!("(for (let {} {}) {} {}", var_name, start, cond, step);
                s += &body.iter().fold(String::new(), |mut acc, n| {
                    acc += &format!(" {}", n);
                    acc
                });
                write!(f, "{})", s)
            }
            Let { name, ty, init } => {
                let mut s = format!("(let {}:{}", name, ty);
                if let Some(body) = init {
                    s += &format!(" {}", body);
                }
                write!(f, "{})", s)
            }
        }
    }
}

#[derive(Debug, PartialEq, Serialize)]
pub(crate) struct Prototype {
    pub(crate) name: String,
    pub(crate) args: Vec<String>,
}

impl Display for Prototype {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = format!("({}", self.name);
        if !self.args.is_empty() {
            for arg in &self.args {
                s += &format!(" {}", arg);
            }
        }
        write!(f, "{})", s)
    }
}

#[derive(Debug, PartialEq, Serialize)]
pub(crate) struct Function {
    pub(crate) proto: Box<Prototype>,
    pub(crate) body: Option<Vec<Expression>>,
}

impl Display for Function {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.body {
            Some(body) if !body.is_empty() => {
                let s = body.iter().fold(String::new(), |mut acc, n| {
                    acc += &format!(" {}", n);
                    acc
                });
                write!(f, "(define {}{})", self.proto, s)
            }
            _ => write!(f, "(define {})", self.proto),
        }
    }
}
