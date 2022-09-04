use serde::Serialize;

use common::{Operator, Type};
pub use prototype::Prototype;
use symbol_table::{symbol, Symbol};

mod display;
pub mod prototype;

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

    pub fn into_nodes(self) -> Vec<T> {
        self.nodes
    }
}

impl<T> Default for Ast<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, PartialEq, Clone, Serialize)]
pub enum Node {
    Stmt(Statement),
    Expr(Expression),
}

impl Node {
    pub fn new<F, T>(cons: F, inner: T) -> Self
    where
        F: Fn(T) -> Self,
    {
        (cons)(inner)
    }

    pub fn ty(&self) -> Option<Type> {
        match self {
            Node::Stmt(_) => None,
            Node::Expr(e) => e.ty(),
        }
    }

    pub fn as_stmt(&self) -> &Statement {
        match self {
            Node::Stmt(s) => s,
            Node::Expr(_) => unreachable!("expected Statement"),
        }
    }

    pub fn to_expr(self) -> Expression {
        match self {
            Node::Stmt(_) => unreachable!("expected Expression"),
            Node::Expr(e) => e,
        }
    }

    pub fn as_expr(&self) -> &Expression {
        match self {
            Node::Stmt(_) => unreachable!("expected Expression"),
            Node::Expr(e) => e,
        }
    }

    pub fn as_expr_mut(&mut self) -> &mut Expression {
        match self {
            Node::Stmt(_) => unreachable!("expected Expression"),
            Node::Expr(e) => e,
        }
    }
}

#[derive(Debug, PartialEq, Clone, Serialize)]
pub enum Statement {
    For {
        start_name: String, // TODO: make this a Statement::Let
        start_antn: Type,
        start_expr: Option<Box<Node>>,
        cond_expr: Box<Node>,
        step_expr: Box<Node>,
        body: Box<Node>,
    },
    Let(Let),
    Fn {
        proto: Box<Prototype>,
        body: Option<Box<Node>>,
    },
    Struct(Struct),
}

#[derive(Debug, PartialEq, Clone, Serialize)]
pub struct Let {
    pub name: String,
    pub antn: Type,
    pub init: Option<Box<Node>>,
}

impl Statement {
    pub fn as_let(&self) -> &Let {
        match self {
            Statement::Let(l) => l,
            _ => unreachable!("expected Expression"),
        }
    }
}

#[derive(Debug, PartialEq, Clone, Serialize)]
pub struct Struct {
    pub name: String,
    pub fields: Vec<Node>,
    pub methods: Vec<Node>,
}

// For new structs
impl From<&Struct> for Symbol {
    fn from(s: &Struct) -> Self {
        let fields = s
            .fields
            .iter()
            .map(|f| {
                let let_stmt = f.as_stmt().as_let();
                (let_stmt.name.to_owned(), let_stmt.antn.to_owned())
            })
            .collect();
        Symbol {
            name: s.name.to_owned(),
            data: symbol::AssocData::Struct(symbol::StructData { fields, methods: None }),
        }
    }
}

#[derive(Debug, PartialEq, Clone, Serialize)]
pub enum Expression {
    Lit { value: Literal, ty: Option<Type> },
    Ident { name: String, ty: Option<Type> },
    BinOp { op: Operator, lhs: Box<Node>, rhs: Box<Node>, ty: Option<Type> },
    UnOp { op: Operator, rhs: Box<Node>, ty: Option<Type> },
    Call { name: String, args: Vec<Node>, ty: Option<Type> },
    Cond { cond_expr: Box<Node>, then_block: Box<Node>, else_block: Option<Box<Node>>, ty: Option<Type> },
    Block { list: Vec<Node>, ty: Option<Type> },
    Index { binding: Box<Node>, idx: Box<Node>, ty: Option<Type> },
}

impl Expression {
    pub fn ty(&self) -> Option<Type> {
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
        .clone()
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

#[derive(Debug, PartialEq, Clone, Serialize)]
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
    Array { elements: Vec<Node>, inner_ty: Option<Type> },
}

#[macro_export]
macro_rules! make_literal {
    (Array, $ty:expr, $len:expr) => {
        Expression::Lit {
            value: Literal::Array { elements: Vec::with_capacity($len), inner_ty: Some(*$ty) },
            ty: Some(Type::Array(Box::new(*$ty), $len)),
        }
    };

    ($ty:tt, $val:expr) => {
        Expression::Lit { value: Literal::$ty($val), ty: Some(Type::$ty) }
    };
}

// Immutable visitor interface

pub trait AstVisitor {
    type Result;

    fn visit_stmt(&mut self, s: Statement) -> Self::Result;
    fn visit_expr(&mut self, e: Expression) -> Self::Result;
}

pub trait Visitable {
    fn accept<V: AstVisitor>(self, v: &mut V) -> V::Result;
}

impl Visitable for Node {
    fn accept<V: AstVisitor>(self, v: &mut V) -> V::Result {
        match self {
            Node::Stmt(s) => v.visit_stmt(s),
            Node::Expr(e) => v.visit_expr(e),
        }
    }
}

impl Visitable for Statement {
    fn accept<V: AstVisitor>(self, v: &mut V) -> V::Result {
        v.visit_stmt(self)
    }
}

impl Visitable for Expression {
    fn accept<V: AstVisitor>(self, v: &mut V) -> V::Result {
        v.visit_expr(self)
    }
}
