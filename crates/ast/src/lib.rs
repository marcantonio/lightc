use serde::Serialize;

use common::{Symbol, Type};
use convert::AsExpr;

pub mod convert;
mod display;

#[derive(Debug, PartialEq, Serialize)]
pub struct Ast<T> {
    nodes: Vec<T>,
}

impl<T> Ast<T> {
    pub fn new() -> Self {
        Ast { nodes: vec![] }
    }

    pub fn add(&mut self, node: T) {
        self.nodes.push(node)
    }

    pub fn nodes(&self) -> &[T] {
        &self.nodes
    }

    pub fn nodes_mut(&mut self) -> &mut [T] {
        &mut self.nodes
    }
}

impl<T> Default for Ast<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, PartialEq, Serialize)]
pub enum Node {
    Stmt(Statement),
    Expr(Expression),
}

impl Node {
    pub fn ty(&self) -> Option<&Type> {
        self.as_expr().ty()
    }
}

#[derive(Debug, PartialEq, Serialize)]
pub enum Statement {
    For {
        start_name: String,
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
        proto: Box<Prototype>,
        body: Option<Box<Node>>,
    },
    Struct {
        name: String,
        attributes: Vec<Node>,
        methods: Vec<Node>,
    }
}

#[derive(Debug, PartialEq, Serialize)]
pub enum Expression {
    Lit {
        value: Literal,
        ty: Option<Type>,
    },
    Ident {
        name: String,
        ty: Option<Type>,
    },
    BinOp {
        sym: Symbol,
        lhs: Box<Node>,
        rhs: Box<Node>,
        ty: Option<Type>,
    },
    UnOp {
        sym: Symbol,
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
}

impl Expression {
    pub fn ty(&self) -> Option<&Type> {
        use Expression::*;

        match self {
            Lit { ty, .. } => ty,
            Ident { ty, .. } => ty,
            BinOp { ty, .. } => ty,
            UnOp { ty, .. } => ty,
            Call { ty, .. } => ty,
            Cond { ty, .. } => ty,
            Block { ty, .. } => ty,
            Index { ty, .. } => ty,
        }
        .as_ref()
    }

    pub fn is_num_literal(&self) -> bool {
        matches!(
            self,
            Expression::Lit {
                value: Literal::Int8(_)
                    | Literal::Int16(_)
                    | Literal::Int32(_)
                    | Literal::Int64(_)
                    | Literal::UInt8(_)
                    | Literal::UInt16(_)
                    | Literal::UInt32(_)
                    | Literal::UInt64(_)
                    | Literal::Float(_)
                    | Literal::Double(_),
                ..
            }
        )
    }
}

#[derive(Debug, PartialEq, Serialize)]
pub enum Literal {
    Int8(i8),
    Int16(i16),
    Int32(i32),
    Int64(i64),
    UInt8(u8),
    UInt16(u16),
    UInt32(u32),
    UInt64(u64),
    Float(f32),
    Double(f64),
    Bool(bool),
    Char(u8),
    Array {
        elements: Vec<Node>,
        inner_ty: Option<Type>,
    },
}

#[derive(Debug, PartialEq, Serialize)]
pub struct Prototype {
    name: String,
    args: Vec<(String, Type)>,
    ret_ty: Option<Type>,
}

impl Prototype {
    pub fn new(name: String, args: Vec<(String, Type)>, ret_ty: Option<Type>) -> Prototype {
        Prototype { name, args, ret_ty }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn set_name(&mut self, name: String) {
        self.name = name;
    }

    pub fn args(&self) -> &[(String, Type)] {
        &self.args
    }

    pub fn set_args(&mut self, args: Vec<(String, Type)>) {
        self.args = args;
    }

    pub fn ret_ty(&self) -> Option<&Type> {
        self.ret_ty.as_ref()
    }

    pub fn set_ret_ty(&mut self, ret_ty: Option<Type>) {
        self.ret_ty = ret_ty;
    }
}

// Immutable visitor interface

pub trait AstVisitor {
    type Result;

    fn visit_stmt(&mut self, s: &Statement) -> Self::Result;
    fn visit_expr(&mut self, e: &Expression) -> Self::Result;
}

pub trait Visitable {
    fn accept<V: AstVisitor>(&self, v: &mut V) -> V::Result;
}

impl Visitable for Node {
    fn accept<V: AstVisitor>(&self, v: &mut V) -> V::Result {
        match self {
            Node::Stmt(s) => v.visit_stmt(s),
            Node::Expr(e) => v.visit_expr(e),
        }
    }
}

impl Visitable for Expression {
    fn accept<V: AstVisitor>(&self, v: &mut V) -> V::Result {
        v.visit_expr(self)
    }
}

impl Visitable for Statement {
    fn accept<V: AstVisitor>(&self, v: &mut V) -> V::Result {
        v.visit_stmt(self)
    }
}

// Mutable visitor interface

pub trait AstVisitorMut {
    type Result;

    fn visit_stmt(&mut self, s: &mut Statement) -> Self::Result;
    fn visit_expr(&mut self, e: &mut Expression) -> Self::Result;
}

pub trait VisitableMut {
    fn accept<V: AstVisitorMut>(&mut self, v: &mut V) -> V::Result;
}

impl VisitableMut for Node {
    fn accept<V: AstVisitorMut>(&mut self, v: &mut V) -> V::Result {
        match self {
            Node::Stmt(s) => v.visit_stmt(s),
            Node::Expr(e) => v.visit_expr(e),
        }
    }
}

impl VisitableMut for Expression {
    fn accept<V: AstVisitorMut>(&mut self, v: &mut V) -> V::Result {
        v.visit_expr(self)
    }
}

impl VisitableMut for Statement {
    fn accept<V: AstVisitorMut>(&mut self, v: &mut V) -> V::Result {
        v.visit_stmt(self)
    }
}
