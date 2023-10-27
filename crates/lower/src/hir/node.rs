use serde::Serialize;
use std::fmt::Display;

use super::VisitableNode;
use common::{Literal, Operator, Prototype, Type};

#[derive(Debug, PartialEq, Clone, Serialize)]
pub struct Node {
    pub kind: Kind,
}

impl Node {
    pub fn new_for(
        start_name: String, start_antn: Type, start_expr: Option<Node>, cond_expr: Node, step_expr: Node,
        body: Node,
    ) -> Self {
        Self {
            kind: Kind::For {
                start_name,
                start_antn,
                start_expr: start_expr.map(Box::new),
                cond_expr: Box::new(cond_expr),
                step_expr: Box::new(step_expr),
                body: Box::new(body),
            },
        }
    }

    pub fn new_loop(body: Node) -> Self {
        Self { kind: Kind::Loop { body: Box::new(body) } }
    }

    pub fn new_let(name: String, antn: Type, init: Option<Node>) -> Self {
        Self { kind: Kind::Let { name, antn, init: init.map(Box::new) } }
    }

    pub fn new_fn(proto: Prototype, body: Option<Node>) -> Self {
        Self { kind: Kind::Fn { proto, body: body.map(Box::new) } }
    }

    pub fn new_lit(value: Literal<Node>, ty: Type) -> Self {
        Self { kind: Kind::Lit { value, ty } }
    }

    pub fn new_ident(name: String, ty: Type) -> Self {
        Self { kind: Kind::Ident { name, ty } }
    }

    pub fn new_binop(op: Operator, lhs: Node, rhs: Node, ty: Type) -> Self {
        Self { kind: Kind::BinOp { op, lhs: Box::new(lhs), rhs: Box::new(rhs), ty } }
    }

    pub fn new_unop(op: Operator, rhs: Node, ty: Type) -> Self {
        Self { kind: Kind::UnOp { op, rhs: Box::new(rhs), ty } }
    }

    pub fn new_call(name: String, args: Vec<Node>, ty: Type) -> Self {
        Self { kind: Kind::Call { name, args, ty } }
    }

    pub fn new_cond(cond_expr: Node, then_block: Node, else_block: Option<Node>, ty: Type) -> Self {
        Self {
            kind: Kind::Cond {
                cond_expr: Box::new(cond_expr),
                then_block: Box::new(then_block),
                else_block: else_block.map(Box::new),
                ty,
            },
        }
    }

    pub fn new_block(list: Vec<Node>, ty: Type) -> Self {
        Self { kind: Kind::Block { list, ty } }
    }

    pub fn new_index(array: Node, idx: Node, ty: Type) -> Self {
        Self { kind: Kind::Index { array: Box::new(array), idx: Box::new(idx), ty } }
    }

    pub fn new_fselector(comp: Node, idx: u32, ty: Type) -> Self {
        Self { kind: Kind::FSelector { comp: Box::new(comp), idx, ty } }
    }

    pub fn new_blank() -> Self {
        Self { kind: Kind::Blank }
    }

    pub fn ty(&self) -> &Type {
        use Kind::*;

        match &self.kind {
            Lit { ty, .. } => ty,
            Ident { ty, .. } => ty,
            BinOp { ty, .. } => ty,
            UnOp { ty, .. } => ty,
            Call { ty, .. } => ty,
            Cond { ty, .. } => ty,
            Block { ty, .. } => ty,
            Index { ty, .. } => ty,
            FSelector { ty, .. } => ty,
            _ => unreachable!("statement found where expression expected"),
        }
    }

    pub fn set_ty(&mut self, new_ty: Type) {
        use Kind::*;

        match &mut self.kind {
            Lit { ty, .. } => *ty = new_ty,
            Ident { ty, .. } => *ty = new_ty,
            BinOp { ty, .. } => *ty = new_ty,
            UnOp { ty, .. } => *ty = new_ty,
            Call { ty, .. } => *ty = new_ty,
            Cond { ty, .. } => *ty = new_ty,
            Block { ty, .. } => *ty = new_ty,
            Index { ty, .. } => *ty = new_ty,
            FSelector { ty, .. } => *ty = new_ty,
            _ => unreachable!("can't set type on statement"),
        }
    }

    pub fn is_num_literal(&self) -> bool {
        use Literal::*;

        matches!(
            self.kind,
            Kind::Lit {
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
            }
        )
    }
}

#[derive(Debug, PartialEq, Clone, Serialize)]
pub enum Kind {
    // Statements
    For {
        start_name: String, // TODO: make this a Statement::Let
        start_antn: Type,
        start_expr: Option<Box<Node>>,
        cond_expr: Box<Node>,
        step_expr: Box<Node>,
        body: Box<Node>,
    },
    Loop {
        body: Box<Node>,
    },
    Let {
        name: String,
        antn: Type,
        init: Option<Box<Node>>,
    },
    Fn {
        proto: Prototype,
        body: Option<Box<Node>>,
    },

    // Expressions
    Lit {
        value: Literal<Node>,
        ty: Type,
    },
    Ident {
        name: String,
        ty: Type,
    },
    BinOp {
        op: Operator,
        lhs: Box<Node>,
        rhs: Box<Node>,
        ty: Type,
    },
    UnOp {
        op: Operator,
        rhs: Box<Node>,
        ty: Type,
    },
    Call {
        name: String,
        args: Vec<Node>,
        ty: Type,
    },
    Cond {
        cond_expr: Box<Node>,
        then_block: Box<Node>,
        else_block: Option<Box<Node>>,
        ty: Type,
    },
    Block {
        list: Vec<Node>,
        ty: Type,
    },
    Index {
        array: Box<Node>,
        idx: Box<Node>,
        ty: Type,
    },
    FSelector {
        comp: Box<Node>,
        idx: u32,
        ty: Type,
    },
    Blank,
}

impl VisitableNode for Node {
    fn accept<V: super::Visitor<AstNode = Self>>(self, v: &mut V) -> V::Result {
        use Kind::*;

        match self.kind {
            For { start_name, start_antn, start_expr, cond_expr, step_expr, body } => {
                v.visit_for(start_name, start_antn, start_expr.map(|x| *x), *cond_expr, *step_expr, *body)
            },
            Let { name, antn, init } => v.visit_let(name, antn, init.map(|x| *x)),
            Loop { body } => v.visit_loop(*body),
            Fn { proto, body } => v.visit_fn(proto, body.map(|x| *x)),
            Lit { value, ty } => v.visit_lit(value, ty),
            Ident { name, ty } => v.visit_ident(name, ty),
            BinOp { op, lhs, rhs, .. } => v.visit_binop(op, *lhs, *rhs),
            UnOp { op, rhs, .. } => v.visit_unop(op, *rhs),
            Call { name, args, .. } => v.visit_call(name, args),
            Cond { cond_expr, then_block, else_block, ty } => {
                v.visit_cond(*cond_expr, *then_block, else_block.map(|x| *x), ty)
            },
            Block { list, .. } => v.visit_block(list),
            Index { array, idx, .. } => v.visit_index(*array, *idx),
            FSelector { comp, idx, .. } => v.visit_fselector(*comp, idx),
            _ => unreachable!("invalid node kind visited"),
        }
    }
}

impl Display for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Kind::*;

        match &self.kind {
            For { start_name, start_antn, start_expr, cond_expr, step_expr, body } => {
                let mut s = format!("(for ({}: {}", start_name, start_antn);
                if let Some(init) = &start_expr {
                    s += &format!(" {}", init);
                }
                write!(f, "{}) {} {} {})", s, cond_expr, step_expr, body)
            },
            Loop { body } => write!(f, "(loop {})", body),
            Let { name, antn, init } => {
                let mut s = format!("(let {}:{}", name, antn);
                if let Some(body) = &init {
                    s += &format!(" {}", body);
                }
                write!(f, "{})", s)
            },
            Fn { proto, body } => match &body {
                Some(body) => write!(f, "(define {} {})", proto, body),
                _ => write!(f, "(define {})", proto),
            },
            Lit { value, .. } => write!(f, "{}", value),
            Ident { name, .. } => write!(f, "{}", name),
            BinOp { op, lhs, rhs, .. } => write!(f, "({} {} {})", op, lhs, rhs),
            UnOp { op, rhs, .. } => write!(f, "({} {})", op, rhs),
            Call { name, args, .. } => {
                let mut s = format!("({}", name);
                if !args.is_empty() {
                    for arg in args {
                        s += &format!(" {}", arg);
                    }
                }
                write!(f, "{})", s)
            },
            Cond { cond_expr, then_block, else_block, .. } => {
                let mut s = format!("(if {} {}", cond_expr, then_block);
                if let Some(alt) = &else_block {
                    s += &format!(" {}", alt);
                }
                write!(f, "{})", s)
            },
            Block { list, .. } => {
                let mut s = "'(".to_string();
                s += &list.iter().fold(String::new(), |mut acc, n| {
                    acc += &format!("{} ", n);
                    acc
                });
                write!(f, "{})", s.strip_suffix(' ').unwrap_or("'()"))
            },
            Index { array, idx, .. } => write!(f, "{}[{}]", array, idx),
            FSelector { comp, idx, .. } => write!(f, "{}.{}", comp, idx),
            Blank => write!(f, "<blank_node>"),
        }
    }
}
