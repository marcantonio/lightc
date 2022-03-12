use std::fmt::Display;

use super::{Node, Expression, Prototype, Statement};

impl Display for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Node::Stmt(stmt) => write!(f, "{}", stmt),
            Node::Expr(expr) => write!(f, "{}", expr),
        }
    }
}

impl Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Statement::*;
        match self {
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
            Fn { proto, body } => {
                match body {
                    Some(body) if !body.is_empty() => {
                        let s = body.iter().fold(String::new(), |mut acc, n| {
                            acc += &format!(" {}", n);
                            acc
                        });
                        write!(f, "(define {}{})", proto, s)
                    }
                    _ => write!(f, "(define {})", proto),
                }
            }
        }
    }
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
        }
    }
}

impl Display for Prototype {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = format!("({}", self.name);
        if !self.args.is_empty() {
            for arg in &self.args {
                s += &format!(" {}:{}", arg.0, arg.1);
            }
        }
        write!(f, "{})", s)
    }
}
