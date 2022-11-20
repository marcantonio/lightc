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

    pub fn new_let(name: String, antn: Type, init: Option<Node>) -> Self {
        Self { kind: Kind::Let { name, antn, init: init.map(Box::new) } }
    }

    pub fn new_fn(proto: Prototype, body: Option<Node>) -> Self {
        Self { kind: Kind::Fn { proto, body: body.map(Box::new) } }
    }

    pub fn new_struct(name: String, fields: Vec<Node>, methods: Vec<Node>) -> Self {
        Self { kind: Kind::Struct { name, fields, methods } }
    }

    pub fn new_lit(value: Literal<Node>, ty: Option<Type>) -> Self {
        Self { kind: Kind::Lit { value, ty } }
    }

    pub fn new_ident(name: String, ty: Option<Type>) -> Self {
        Self { kind: Kind::Ident { name, ty } }
    }

    pub fn new_binop(op: Operator, lhs: Node, rhs: Node, ty: Option<Type>) -> Self {
        Self { kind: Kind::BinOp { op, lhs: Box::new(lhs), rhs: Box::new(rhs), ty } }
    }

    pub fn new_unop(op: Operator, rhs: Node, ty: Option<Type>) -> Self {
        Self { kind: Kind::UnOp { op, rhs: Box::new(rhs), ty } }
    }

    pub fn new_call(name: String, args: Vec<Node>, ty: Option<Type>) -> Self {
        Self { kind: Kind::Call { name, args, ty } }
    }

    pub fn new_cond(cond_expr: Node, then_block: Node, else_block: Option<Node>, ty: Option<Type>) -> Self {
        Self {
            kind: Kind::Cond {
                cond_expr: Box::new(cond_expr),
                then_block: Box::new(then_block),
                else_block: else_block.map(Box::new),
                ty,
            },
        }
    }

    pub fn new_block(list: Vec<Node>, ty: Option<Type>) -> Self {
        Self { kind: Kind::Block { list, ty } }
    }

    pub fn new_index(binding: Node, idx: Node, ty: Option<Type>) -> Self {
        Self { kind: Kind::Index { binding: Box::new(binding), idx: Box::new(idx), ty } }
    }

    pub fn new_fselector(comp: Node, field: String, ty: Option<Type>) -> Self {
        Self { kind: Kind::FSelector { comp: Box::new(comp), field, ty } }
    }

    pub fn new_mselector(comp: Node, method: String, args: Vec<Node>, ty: Option<Type>) -> Self {
        Self { kind: Kind::MSelector { comp: Box::new(comp), method, args, ty } }
    }

    pub fn ty(&self) -> Option<&Type> {
        use Kind::*;

        match &self.kind {
            Lit { ty, .. } => ty.as_ref(),
            Ident { ty, .. } => ty.as_ref(),
            BinOp { ty, .. } => ty.as_ref(),
            UnOp { ty, .. } => ty.as_ref(),
            Call { ty, .. } => ty.as_ref(),
            Cond { ty, .. } => ty.as_ref(),
            Block { ty, .. } => ty.as_ref(),
            Index { ty, .. } => ty.as_ref(),
            FSelector { ty, .. } => ty.as_ref(),
            MSelector { ty, .. } => ty.as_ref(),
            _ => None,
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
    Let {
        name: String,
        antn: Type,
        init: Option<Box<Node>>,
    },
    Fn {
        proto: Prototype,
        body: Option<Box<Node>>,
    },
    Struct {
        name: String,
        fields: Vec<Node>,
        methods: Vec<Node>,
    },

    // Expressions
    Lit {
        value: Literal<Node>,
        ty: Option<Type>,
    },
    Ident {
        name: String,
        ty: Option<Type>,
    },
    BinOp {
        op: Operator,
        lhs: Box<Node>,
        rhs: Box<Node>,
        ty: Option<Type>,
    },
    UnOp {
        op: Operator,
        rhs: Box<Node>,
        ty: Option<Type>,
    },
    Call {
        name: String,
        args: Vec<Node>,
        ty: Option<Type>,
    },
    Cond {
        cond_expr: Box<Node>,
        then_block: Box<Node>,
        else_block: Option<Box<Node>>,
        ty: Option<Type>,
    },
    Block {
        list: Vec<Node>,
        ty: Option<Type>,
    },
    Index {
        binding: Box<Node>,
        idx: Box<Node>,
        ty: Option<Type>,
    },
    FSelector {
        comp: Box<Node>,
        field: String,
        ty: Option<Type>,
    },
    MSelector {
        comp: Box<Node>,
        method: String,
        args: Vec<Node>,
        ty: Option<Type>,
    },
}

impl VisitableNode for Node {
    fn accept<V: super::Visitor<AstNode = Self>>(self, v: &mut V) -> V::Result {
        use Kind::*;

        match self.kind {
            For { start_name, start_antn, start_expr, cond_expr, step_expr, body } => {
                v.visit_for(start_name, start_antn, start_expr.map(|x| *x), *cond_expr, *step_expr, *body)
            },
            Let { name, antn, init } => v.visit_let(name, antn, init.map(|x| *x)),
            Fn { proto, body } => v.visit_fn(proto, body.map(|x| *x)),
            Struct { name, fields, methods } => v.visit_struct(name, fields, methods),
            Lit { value, ty } => v.visit_lit(value, ty),
            Ident { name, ty } => v.visit_ident(name, ty),
            BinOp { op, lhs, rhs, ty } => v.visit_binop(op, *lhs, *rhs, ty),
            UnOp { op, rhs, ty } => v.visit_unop(op, *rhs, ty),
            Call { name, args, ty } => v.visit_call(name, args, ty),
            Cond { cond_expr, then_block, else_block, ty } => {
                v.visit_cond(*cond_expr, *then_block, else_block.map(|x| *x), ty)
            },
            Block { list, ty } => v.visit_block(list, ty),
            Index { binding, idx, ty } => v.visit_index(*binding, *idx, ty),
            FSelector { comp, field, ty } => v.visit_fselector(*comp, field, ty),
            MSelector { comp: _, method: _, args: _, ty: _ } => todo!(),
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
            Struct { name, fields, methods } => {
                let mut attr_string = String::from("");
                attr_string += &fields.iter().fold(String::new(), |mut acc, n| {
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
            Index { binding, idx, .. } => write!(f, "{}[{}]", binding, idx),
            FSelector { comp, field, .. } => write!(f, "{}.{}", comp, field),
            MSelector { comp, method, args, .. } => {
                let mut s = format!("({}.{}", comp, method);
                if !args.is_empty() {
                    for arg in args {
                        s += &format!(" {}", arg);
                    }
                }
                write!(f, "{})", s)
            },
        }
    }
}
