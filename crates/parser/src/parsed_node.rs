use std::fmt::Display;

use ast::*;
use serde::Serialize;

#[derive(Debug, PartialEq, Clone, Serialize)]
pub struct ParsedNode {
    pub node: NodeKind<ParsedNode>,
}

// pub enum ParsedNode {
//     For(For<ParsedNode>),
//     Let(Let<ParsedNode>),
//     Fn(Fn<ParsedNode>),
//     Struct(Struct<ParsedNode>),
//     Lit(Lit<ParsedNode>),
//     Ident(Ident),
//     BinOp(BinOp<ParsedNode>),
//     UnOp(UnOp<ParsedNode>),
//     Call(Call<ParsedNode>),
//     Cond(Cond<ParsedNode>),
//     Block(Block<ParsedNode>),
//     Index(Index<ParsedNode>),
// }

impl ParsedNode {
    pub fn is_num_literal(&self) -> bool {
        use Literal::*;

        matches!(
            self.node,
            NodeKind::Lit(Lit {
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
        use NodeKind::*;
        match &self.node {
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
        use NodeKind::*;

        match self.node {
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
