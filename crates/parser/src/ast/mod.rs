use std::fmt::Display;

use serde::Serialize;

pub mod prototype;
pub use prototype::Prototype;
pub mod stmt;
pub use stmt::*;
pub mod expr;
pub use expr::*;

#[derive(Debug, PartialEq, Serialize)]
pub struct Ast<T: Node> {
    nodes: Vec<T>,
}

impl<T: Node> Ast<T> {
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

impl<T: Node> Default for Ast<T> {
    fn default() -> Self {
        Self::new()
    }
}

// Immutable visitor interface

pub trait AstVisitor {
    type Node: Node;
    type Result;

    fn visit_for(&mut self, s: For<Self::Node>) -> Self::Result;
    fn visit_let(&mut self, s: Let<Self::Node>) -> Self::Result;
    fn visit_fn(&mut self, s: Fn<Self::Node>) -> Self::Result;
    fn visit_struct(&mut self, s: Struct<Self::Node>) -> Self::Result;
    fn visit_lit(&mut self, e: Lit<Self::Node>) -> Self::Result;
    fn visit_binop(&mut self, e: BinOp<Self::Node>) -> Self::Result;
    fn visit_unop(&mut self, e: UnOp<Self::Node>) -> Self::Result;
    fn visit_ident(&mut self, e: Ident) -> Self::Result;
    fn visit_call(&mut self, e: Call<Self::Node>) -> Self::Result;
    fn visit_cond(&mut self, e: Cond<Self::Node>) -> Self::Result;
    fn visit_block(&mut self, e: Block<Self::Node>) -> Self::Result;
    fn visit_index(&mut self, e: Index<Self::Node>) -> Self::Result;
}

pub trait Visitable {
    fn accept<V>(self, v: &mut V) -> V::Result
    where
        V: AstVisitor<Node = Self>;
}

pub trait Node {}

#[derive(Debug, PartialEq, Clone, Serialize)]
pub enum ParsedNode {
    // Statements
    For(For<ParsedNode>),
    Let(Let<ParsedNode>),
    Fn(Fn<ParsedNode>),
    Struct(Struct<ParsedNode>),
    // Expressions
    Lit(Lit<ParsedNode>),
    Ident(Ident),
    BinOp(BinOp<ParsedNode>),
    UnOp(UnOp<ParsedNode>),
    Call(Call<ParsedNode>),
    Cond(Cond<ParsedNode>),
    Block(Block<ParsedNode>),
    Index(Index<ParsedNode>),
}

impl ParsedNode {
    pub fn new<F, T>(cons: F, inner: T) -> Self
    where
        F: core::ops::Fn(T) -> Self,
    {
        (cons)(inner)
    }

    pub fn is_num_literal(&self) -> bool {
        use Literal::*;

        matches!(
            self,
            Self::Lit(Lit {
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
            })
        )
    }
}

impl Node for ParsedNode {}

impl Display for ParsedNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use ParsedNode::*;
        match self {
            For(s) => write!(f, "{}", s),
            Let(s) => write!(f, "{}", s),
            Fn(s) => write!(f, "{}", s),
            Struct(s) => write!(f, "{}", s),
            Lit(e) => write!(f, "{}", e),
            BinOp(e) => write!(f, "{}", e),
            UnOp(e) => write!(f, "{}", e),
            Ident(e) => write!(f, "{}", e),
            Call(e) => write!(f, "{}", e),
            Cond(e) => write!(f, "{}", e),
            Block(e) => write!(f, "{}", e),
            Index(e) => write!(f, "{}", e),
        }
    }
}

impl Visitable for ParsedNode {
    fn accept<V: AstVisitor<Node = Self>>(self, v: &mut V) -> V::Result {
        use ParsedNode::*;

        match self {
            For(s) => v.visit_for(s),
            Let(s) => v.visit_let(s),
            Fn(s) => v.visit_fn(s),
            Struct(s) => v.visit_struct(s),
            Lit(e) => v.visit_lit(e),
            BinOp(e) => v.visit_binop(e),
            UnOp(e) => v.visit_unop(e),
            Ident(e) => v.visit_ident(e),
            Call(e) => v.visit_call(e),
            Cond(e) => v.visit_cond(e),
            Block(e) => v.visit_block(e),
            Index(e) => v.visit_index(e),
        }
    }
}
