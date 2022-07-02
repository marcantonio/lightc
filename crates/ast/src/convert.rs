use super::*;

pub trait AsNodeType<T: ?Sized> {
    fn as_node_type(&self) -> &T;
}

impl AsNodeType<Expression> for Node {
    fn as_node_type(&self) -> &Expression {
        match self {
            Node::Stmt(_) => unreachable!("fatal: expected Expression"),
            Node::Expr(e) => e,
        }
    }
}

impl AsNodeType<Expression> for Box<Node> {
    fn as_node_type(&self) -> &Expression {
        (**self).as_expr()
    }
}

impl AsNodeType<Expression> for Expression {
    fn as_node_type(&self) -> &Expression {
        self
    }
}

pub trait AsNodeTypeMut<T: ?Sized> {
    fn as_node_type_mut(&self) -> &T;
}

impl AsNodeTypeMut<Expression> for Node {
    fn as_node_type_mut(&self) -> &Expression {
        match self {
            Node::Stmt(_) => unreachable!("fatal: expected Expression"),
            Node::Expr(e) => e,
        }
    }
}

impl AsNodeTypeMut<Expression> for Box<Node> {
    fn as_node_type_mut(&self) -> &Expression {
        (**self).as_expr()
    }
}

impl AsNodeTypeMut<Expression> for Expression {
    fn as_node_type_mut(&self) -> &Expression {
        self
    }
}

/// As immutable expressions

pub trait AsExpr<T: ?Sized> {
    fn as_expr(&self) -> &T;
}

impl AsExpr<Expression> for Node {
    fn as_expr(&self) -> &Expression {
        match self {
            Node::Stmt(_) => unreachable!("fatal: expected Expression"),
            Node::Expr(e) => e,
        }
    }
}

impl AsExpr<Expression> for Box<Node> {
    fn as_expr(&self) -> &Expression {
        (**self).as_expr()
    }
}

impl AsExpr<Expression> for Expression {
    fn as_expr(&self) -> &Expression {
        self
    }
}

/// As mutable expressions

pub trait AsExprMut<T: ?Sized> {
    fn as_expr_mut(&mut self) -> &mut T;
}

impl AsExprMut<Expression> for Node {
    fn as_expr_mut(&mut self) -> &mut Expression {
        match self {
            Node::Stmt(_) => unreachable!("fatal: expected Expression"),
            Node::Expr(e) => e,
        }
    }
}

impl AsExprMut<Expression> for Box<Node> {
    fn as_expr_mut(&mut self) -> &mut Expression {
        (**self).as_expr_mut()
    }
}

impl AsExprMut<Expression> for Expression {
    fn as_expr_mut(&mut self) -> &mut Expression {
        self
    }
}
