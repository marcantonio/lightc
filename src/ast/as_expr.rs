use super::*;

// As immutable expresions

pub(crate) trait AsExpr<'a> {
    type Item;

    fn as_expr(&'a self) -> Result<Self::Item, String>;
}

impl<'a> AsExpr<'a> for Node {
    type Item = &'a Expression;

    fn as_expr(&'a self) -> Result<Self::Item, String> {
        match self {
            Node::Stmt(_) => Err("Expected expresion in node. Found statement.".to_string()),
            Node::Expr(e) => Ok(e),
        }
    }
}

impl<'a> AsExpr<'a> for Box<Node> {
    type Item = &'a Expression;

    fn as_expr(&'a self) -> Result<Self::Item, String> {
        (**self).as_expr()
    }
}

impl<'a> AsExpr<'a> for Option<Box<Node>> {
    type Item = Option<&'a Expression>;

    fn as_expr(&'a self) -> Result<Self::Item, String> {
        self.as_deref().map(Node::as_expr).transpose()
    }
}

impl<'a> AsExpr<'a> for Vec<Node> {
    type Item = Vec<&'a Expression>;

    fn as_expr(&'a self) -> Result<Self::Item, String> {
        self.iter().map(|n| n.as_expr()).collect()
    }
}

impl<'a> AsExpr<'a> for Option<Vec<Node>> {
    type Item = Option<Vec<&'a Expression>>;

    fn as_expr(&'a self) -> Result<Self::Item, String> {
        self.as_ref().map(|o| o.as_expr()).transpose()
    }
}

// As mutable expresions

pub(crate) trait AsExprMut<'a> {
    type Item;

    fn as_expr_mut(&'a mut self) -> Result<Self::Item, String>;
}

impl<'a> AsExprMut<'a> for Node {
    type Item = &'a mut Expression;

    fn as_expr_mut(&'a mut self) -> Result<Self::Item, String> {
        match self {
            Node::Stmt(_) => Err("Expected expresion in node. Found statement.".to_string()),
            Node::Expr(e) => Ok(e),
        }
    }
}

impl<'a> AsExprMut<'a> for Option<Box<Node>> {
    type Item = Option<&'a mut Expression>;

    fn as_expr_mut(&'a mut self) -> Result<Self::Item, String> {
        self.as_deref_mut().map(Node::as_expr_mut).transpose()
    }
}

impl<'a> AsExprMut<'a> for Vec<Node> {
    type Item = Vec<&'a mut Expression>;

    fn as_expr_mut(&'a mut self) -> Result<Self::Item, String> {
        self.iter_mut().map(|n| n.as_expr_mut()).collect()
    }
}
