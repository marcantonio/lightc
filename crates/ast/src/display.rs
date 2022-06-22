use std::fmt::Display;

use super::{Expression, Literal, Node, Prototype, Statement};

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
            For {
                start_name,
                start_antn,
                start_expr,
                cond_expr,
                step_expr,
                body,
            } => {
                let mut s = format!(
                    "(for ({}: {}",
                    start_name, start_antn
                );
                if let Some(init) = start_expr {
                    s += &format!(" {}", init);
                }
                write!(f, "{}) {} {} {})", s, cond_expr, step_expr, body)
            }
            Let { name, antn, init } => {
                let mut s = format!("(let {}:{}", name, antn);
                if let Some(body) = init {
                    s += &format!(" {}", body);
                }
                write!(f, "{})", s)
            }
            Fn { proto, body } => match body {
                Some(body) => write!(f, "(define {} {})", proto, body),
                _ => write!(f, "(define {})", proto),
            },
            Struct {
                name,
                attributes,
                methods,
            } => {
                let mut attr_string = String::from("");
                attr_string += &attributes.iter().fold(String::new(), |mut acc, n| {
                    acc += &format!("{} ", n);
                    acc
                });

                let mut meth_string = String::from("");
                meth_string += &methods.iter().fold(String::new(), |mut acc, n| {
                    acc += &format!("{} ", n);
                    acc
                });

                write!(
                    f,
                    "(struct {} '({}) '({}))",
                    name,
                    attr_string.strip_suffix(' ').unwrap_or(""),
                    meth_string.strip_suffix(' ').unwrap_or("")
                )
            }
        }
    }
}

impl Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Expression::*;

        match self {
            Lit { value, .. } => write!(f, "{}", value),
            BinOp { sym, lhs, rhs, .. } => write!(f, "({} {} {})", sym, lhs, rhs),
            UnOp { sym, rhs, .. } => write!(f, "({} {})", sym, rhs),
            Ident { name, .. } => write!(f, "{}", name),
            Call { name, args, .. } => {
                let mut s = format!("({}", name);
                if !args.is_empty() {
                    for arg in args {
                        s += &format!(" {}", arg);
                    }
                }
                write!(f, "{})", s)
            }
            Cond {
                cond_expr,
                then_block,
                else_block,
                ..
            } => {
                let mut s = format!("(if {} {}", cond_expr, then_block);
                if let Some(alt) = else_block {
                    s += &format!(" {}", alt);
                }
                write!(f, "{})", s)
            }
            Block { list, .. } => {
                let mut s = "'(".to_string();
                s += &list.iter().fold(String::new(), |mut acc, n| {
                    acc += &format!("{} ", n);
                    acc
                });
                write!(f, "{})", s.strip_suffix(' ').unwrap_or("'()"))
            }
            Index { binding, idx, .. } => write!(f, "{}[{}]", binding, idx),
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

impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Literal::*;

        match self {
            Int8(v) => write!(f, "{}", v),
            Int16(v) => write!(f, "{}", v),
            Int32(v) => write!(f, "{}", v),
            Int64(v) => write!(f, "{}", v),
            UInt8(v) => write!(f, "{}", v),
            UInt16(v) => write!(f, "{}", v),
            UInt32(v) => write!(f, "{}", v),
            UInt64(v) => write!(f, "{}", v),
            Float(v) => write!(f, "{}", v),
            Double(v) => write!(f, "{}", v),
            Bool(v) => write!(f, "{}", v),
            Char(v) => write!(f, "{}", *v as char),
            Array { elements: el, .. } => {
                let mut s = String::from("[");
                if !el.is_empty() {
                    for e in el {
                        s += &format!(" {}", e);
                    }
                }
                write!(f, "{}]", s)
            }
        }
    }
}
