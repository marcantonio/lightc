use crate::codegen::Expression;
use crate::codegen::Node;

impl TryFrom<Node> for Expression {
    type Error = String;

    fn try_from(value: Node) -> Result<Self, Self::Error> {
        match value {
            Node::Stmt(_) => Err("Expected expresion in node. Found statement.".to_string()),
            Node::Expr(e) => Ok(e),
        }
    }
}

// impl TryFrom<Box<Node>> for Expression {
//     type Error = String;

//     fn try_from(value: Box<Node>) -> Result<Self, Self::Error> {
//         (*value).try_into()
//     }
// }

// impl TryFrom<Box<Node>> for Box<Expression> {
//     type Error = String;

//     fn try_from(value: Box<Node>) -> Result<Self, Self::Error> {
//         value.try_into()
//     }
// }

// impl TryFrom<Option<Box<Node>>> for Expression {
//     type Error = String;

//     fn try_from(value: Option<Box<Node>>) -> Result<Self, Self::Error> {
//         match value {
//             Some(node) => node.try_into(),
//             None => Err("Expected expression. Found empty node.".to_string()),
//         }
//     }
// }

pub(crate) trait ToExpr {
    type Item;

    fn to_expr(self) -> Result<Self::Item, String>;
}

impl ToExpr for Node {
    type Item = Expression;

    fn to_expr(self) -> Result<Self::Item, String> {
        self.try_into()
    }
}

impl ToExpr for Box<Node> {
    type Item = Expression;

    fn to_expr(self) -> Result<Self::Item, String> {
        (*self).try_into()
    }
}

impl ToExpr for Option<Box<Node>> {
    type Item = Option<Expression>;

    fn to_expr(self) -> Result<Self::Item, String> {
        self.map(Box::to_expr).transpose()
    }
}

impl ToExpr for Vec<Node> {
    type Item = Vec<Expression>;

    fn to_expr(self) -> Result<Self::Item, String> {
        self.into_iter().map(|n| n.try_into()).collect()
    }
}

impl ToExpr for Option<Vec<Node>> {
    type Item = Option<Vec<Expression>>;

    fn to_expr(self) -> Result<Self::Item, String> {
        self.map(Vec::to_expr).transpose()
    }
}
