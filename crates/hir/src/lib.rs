use ast::{Ast, AstVisitor, Expression, Literal, Node, Prototype, Statement, Visitable};
use common::{Operator, Type};
use symbol_table::{Symbol, SymbolTable, Symbolic};

#[cfg(test)]
mod tests;

// Performs the following:
// - desugars x += 1 to x = x + 1
// - initializes uninitialized variables
// - makes initial symbol table entries

type StmtResult = Result<Statement, String>;
type ExprResult = Result<Expression, String>;

pub struct Hir<'a> {
    symbol_table: &'a mut SymbolTable<Symbol>,
    ast: Ast<Node>,
}

impl<'a> AstVisitor for Hir<'a> {
    type Result = Result<Node, String>;

    fn visit_stmt(&mut self, s: Statement) -> Self::Result {
        self.lower_stmt(s)
    }

    fn visit_expr(&mut self, e: Expression) -> Self::Result {
        self.lower_expr(e)
    }
}

impl<'a> Hir<'a> {
    pub fn new(symbol_table: &'a mut SymbolTable<Symbol>) -> Self {
        Hir { symbol_table, ast: Ast::new() }
    }

    pub fn walk(mut self, ast: Ast<Node>) -> Result<Ast<Node>, String> {
        for node in ast.into_nodes() {
            let hir_node = node.accept(&mut self)?;
            self.ast.add(hir_node)
        }
        Ok(self.ast)
    }

    fn lower_node(&mut self, node: Node) -> Result<Node, String> {
        Ok(match node {
            Node::Stmt(s) => self.lower_stmt(s)?,
            Node::Expr(e) => self.lower_expr(e)?,
        })
    }

    fn lower_stmt(&mut self, stmt: Statement) -> Result<Node, String> {
        use Statement::*;

        let stmt = match stmt {
            For { start_name, start_antn, start_expr, cond_expr, step_expr, body } => {
                self.lower_for(start_name, start_antn, start_expr, *cond_expr, *step_expr, *body)?
            },
            Let(l) => self.lower_let(l)?,
            Fn { proto, body } => self.lower_func(*proto, body)?,
            Struct(s) => self.lower_struct(s)?,
        };

        Ok(Node::Stmt(stmt))
    }

    fn lower_for(
        &mut self, start_name: String, start_antn: Type, start_expr: Option<Box<Node>>, cond_expr: Node,
        step_expr: Node, body: Node,
    ) -> StmtResult {
        // Insert start var
        self.symbol_table.enter_scope();
        self.symbol_table.insert(Symbol::from((start_name.as_str(), &start_antn)));

        let start_expr = self.lower_var_init(start_expr, &start_antn)?;
        let cond_expr = self.lower_node(cond_expr)?;
        let step_expr = self.lower_node(step_expr)?;
        let body = self.lower_node(body)?;

        self.symbol_table.leave_scope();

        Ok(Statement::For {
            start_name,
            start_antn,
            start_expr: Some(Box::new(start_expr)),
            cond_expr: Box::new(cond_expr),
            step_expr: Box::new(step_expr),
            body: Box::new(body),
        })
    }

    fn lower_let(&mut self, l: ast::Let) -> StmtResult {
        self.symbol_table.insert(Symbol::from((l.name.as_str(), &l.antn)));
        let init_node = self.lower_var_init(l.init, &l.antn)?;
        Ok(Statement::Let(ast::Let { name: l.name, antn: l.antn, init: Some(Box::new(init_node)) }))
    }

    fn lower_func(&mut self, proto: Prototype, body: Option<Box<Node>>) -> StmtResult {
        if self.symbol_table.insert(proto.name(), proto.clone().into()).is_some() {
            return Err(format!("Function `{}` can't be redefined", proto.name()));
        }

        // This creates an interstitial scope for the arguments in the function definition
        // because lower_block() will also create a new scope. Shouldn't be a practical
        // issue.
        self.symbol_table.enter_scope();

        for arg in proto.args() {
            self.symbol_table.insert(Symbol::from(arg));
        }

        let body_node = body.map(|e| self.lower_node(*e));

        self.symbol_table.leave_scope();

        Ok(Statement::Fn { proto: Box::new(proto), body: body_node.transpose()?.map(Box::new) })
    }

    // XXX: struct stuff
    fn lower_struct(&mut self, s: ast::Struct) -> StmtResult {
        // TODO: check for global scope
        dbg!(&s);

        if self.symbol_table.insert(Symbol::from(&s)).is_some() {
            return Err(format!("Struct `{}` can't be redefined", s.name));
        }

        let mut lowered_attrs = vec![];
        for node in s.fields {
            lowered_attrs.push(self.lower_node(node)?);
        }

        let mut lowered_meths = vec![];
        for node in s.methods {
            lowered_meths.push(self.lower_node(node)?);
        }
        Ok(Statement::Struct(ast::Struct { name: s.name, fields: lowered_attrs, methods: lowered_meths }))
    }

    fn lower_expr(&mut self, expr: Expression) -> Result<Node, String> {
        use Expression::*;

        let expr = match expr {
            Ident { name, .. } => self.lower_ident(name)?,
            BinOp { op, lhs, rhs, ty } => self.lower_binop(op, *lhs, *rhs, ty)?,
            UnOp { op, rhs, ty } => self.lower_unop(op, *rhs, ty)?,
            Call { name, args, ty } => self.lower_call(name, args, ty)?,
            Cond { cond_expr, then_block, else_block, ty } => {
                self.lower_cond(*cond_expr, *then_block, else_block, ty)?
            },
            Block { list, ty } => self.lower_block(list, ty)?,
            Index { binding, idx, ty } => self.lower_index(*binding, *idx, ty)?,
            e => e, // some expressions don't contain other nodes
        };

        Ok(Node::Expr(expr))
    }

    fn lower_ident(&mut self, name: String) -> ExprResult {
        self.symbol_table.get(&name).ok_or(format!("Unknown variable: `{}`", name))?;
        Ok(Expression::Ident { name, ty: None })
    }

    // Lower `x += 1` to `x = x + 1`
    fn lower_binop(&mut self, op: Operator, lhs: Node, rhs: Node, ty: Option<Type>) -> ExprResult {
        use Operator::*;

        let orig_lhs = lhs.clone();
        let orig_ty = ty.clone();

        let top_op;
        let rhs = match op {
            AddEq => {
                top_op = Assign;
                Node::Expr(Expression::BinOp { op: Add, lhs: Box::new(lhs), rhs: Box::new(rhs), ty })
            },
            SubEq => {
                top_op = Assign;
                Node::Expr(Expression::BinOp { op: Sub, lhs: Box::new(lhs), rhs: Box::new(rhs), ty })
            },
            MulEq => {
                top_op = Assign;
                Node::Expr(Expression::BinOp { op: Mul, lhs: Box::new(lhs), rhs: Box::new(rhs), ty })
            },
            DivEq => {
                top_op = Assign;
                Node::Expr(Expression::BinOp { op: Div, lhs: Box::new(lhs), rhs: Box::new(rhs), ty })
            },
            _ => {
                top_op = op;
                rhs
            },
        };

        Ok(Expression::BinOp {
            op: top_op,
            lhs: Box::new(self.lower_node(orig_lhs)?),
            rhs: Box::new(self.lower_node(rhs)?),
            ty: orig_ty,
        })
    }

    fn lower_unop(&mut self, op: Operator, rhs: Node, ty: Option<Type>) -> ExprResult {
        Ok(Expression::UnOp { op, rhs: Box::new(self.lower_node(rhs)?), ty })
    }

    fn lower_call(&mut self, name: String, args: Vec<Node>, ty: Option<Type>) -> ExprResult {
        self.symbol_table.get(&name).ok_or(format!("Call to undefined function: `{}`", name))?;

        let mut lowered_args = vec![];
        for node in args {
            lowered_args.push(self.lower_node(node)?);
        }
        Ok(Expression::Call { name, args: lowered_args, ty })
    }

    fn lower_cond(
        &mut self, cond_expr: Node, then_block: Node, else_block: Option<Box<Node>>, ty: Option<Type>,
    ) -> ExprResult {
        Ok(Expression::Cond {
            cond_expr: Box::new(self.lower_node(cond_expr)?),
            then_block: Box::new(self.lower_node(then_block)?),
            else_block: else_block.map(|e| self.lower_node(*e)).transpose()?.map(Box::new),
            ty,
        })
    }

    fn lower_block(&mut self, list: Vec<Node>, ty: Option<Type>) -> ExprResult {
        self.symbol_table.enter_scope();

        let mut lowered_list = vec![];
        for node in list {
            lowered_list.push(self.lower_node(node)?);
        }

        self.symbol_table.leave_scope();

        Ok(Expression::Block { list: lowered_list, ty })
    }

    fn lower_index(&mut self, binding: Node, idx: Node, ty: Option<Type>) -> ExprResult {
        Ok(Expression::Index {
            binding: Box::new(self.lower_node(binding)?),
            idx: Box::new(self.lower_node(idx)?),
            ty,
        })
    }

    // Helper for variable initializations
    fn lower_var_init(&mut self, init: Option<Box<Node>>, antn: &Type) -> Result<Node, String> {
        use Type::*;

        let init_node = if let Some(init) = init {
            self.lower_node(*init)?
        } else {
            let literal = match antn {
                Int8 => ast::make_literal!(Int8, 0),
                Int16 => ast::make_literal!(Int16, 0),
                Int32 => ast::make_literal!(Int32, 0),
                Int64 => ast::make_literal!(Int64, 0),
                UInt8 => ast::make_literal!(UInt8, 0),
                UInt16 => ast::make_literal!(UInt16, 0),
                UInt32 => ast::make_literal!(UInt32, 0),
                UInt64 => ast::make_literal!(UInt64, 0),
                Float => ast::make_literal!(Float, 0.0),
                Double => ast::make_literal!(Double, 0.0),
                Char => ast::make_literal!(Char, 0),
                Bool => ast::make_literal!(Bool, false),
                Array(ty, len) => ast::make_literal!(Array, ty.clone(), *len),
                Void => unreachable!("void type for variable initialization annotation"),
                Comp(_) => todo!(),
            };
            Node::new(Node::Expr, literal)
        };
        Ok(init_node)
    }
}
