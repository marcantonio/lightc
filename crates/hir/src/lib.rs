use ast::{Ast, AstVisitor, Expression, Node, Statement, Visitable};
use common::Operator;
use symbol_table::{Symbol, SymbolTable, Symbolic};

#[cfg(test)]
mod tests;

// Performs the following:
// - desugars x += 1 to x = x + 1
// - cooks function names in the AST and symbol table
// - tracks scope (needed?)

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
            For(s) => self.lower_for(s)?,
            Let(s) => self.lower_let(s)?,
            Fn(s) => self.lower_func(s)?,
            Struct(s) => self.lower_struct(s)?,
        };

        Ok(Node::Stmt(stmt))
    }

    fn lower_for(&mut self, stmt: ast::For) -> StmtResult {
        // Insert start var
        self.symbol_table.enter_scope();
        self.symbol_table.insert(Symbol::from((stmt.start_name.as_str(), &stmt.start_antn)));

        let start_expr = self.lower_var_init(&stmt.start_name, stmt.start_expr)?;
        let cond_expr = self.lower_node(*stmt.cond_expr)?;
        let step_expr = self.lower_node(*stmt.step_expr)?;
        let body = self.lower_node(*stmt.body)?;

        self.symbol_table.leave_scope();

        Ok(Statement::For(ast::For {
            start_name: stmt.start_name,
            start_antn: stmt.start_antn,
            start_expr: Some(Box::new(start_expr)),
            cond_expr: Box::new(cond_expr),
            step_expr: Box::new(step_expr),
            body: Box::new(body),
        }))
    }

    fn lower_let(&mut self, stmt: ast::Let) -> StmtResult {
        self.symbol_table.insert(Symbol::from((stmt.name.as_str(), &stmt.antn)));
        let init_node = self.lower_var_init(&stmt.name, stmt.init)?;
        Ok(Statement::Let(ast::Let { name: stmt.name, antn: stmt.antn, init: Some(Box::new(init_node)) }))
    }

    fn lower_func(&mut self, mut stmt: ast::Fn) -> StmtResult {
        // Insert a duplicate of the symbol. The new one will have the lowered
        // name. Update the AST as well. Skip for externs.
        let sym =
            self.symbol_table.get(stmt.proto.name()).cloned().unwrap_or_else(|| {
                unreachable!("missing symbol in `lower_func()` for `{}`", stmt.proto.name())
            });

        if !sym.is_extern() {
            stmt.proto.set_name(sym.name().to_owned());
            self.symbol_table.insert(sym);
        }

        // This creates an interstitial scope for the arguments in the function definition
        // because lower_block() will also create a new scope. Shouldn't be a practical
        // issue.
        self.symbol_table.enter_scope();

        for arg in stmt.proto.args() {
            self.symbol_table.insert(Symbol::from(arg));
        }

        let body_node = stmt.body.map(|e| self.lower_node(*e));

        self.symbol_table.leave_scope();

        Ok(Statement::Fn(ast::Fn { proto: stmt.proto, body: body_node.transpose()?.map(Box::new) }))
    }

    // XXX: struct stuff
    fn lower_struct(&mut self, stmt: ast::Struct) -> StmtResult {
        // TODO: check for global scope
        //dbg!(&s);

        if self.symbol_table.insert(Symbol::from(&stmt)).is_some() {
            return Err(format!("struct `{}` can't be redefined", stmt.name));
        }

        let mut lowered_attrs = vec![];
        for node in stmt.fields {
            lowered_attrs.push(self.lower_node(node)?);
        }

        let mut lowered_meths = vec![];
        for node in stmt.methods {
            lowered_meths.push(self.lower_node(node)?);
        }

        Ok(Statement::Struct(ast::Struct { name: stmt.name, fields: lowered_attrs, methods: lowered_meths }))
    }

    fn lower_expr(&mut self, expr: Expression) -> Result<Node, String> {
        use Expression::*;

        let expr = match expr {
            Ident(e) => self.lower_ident(e)?,
            BinOp(e) => self.lower_binop(e)?,
            UnOp(e) => self.lower_unop(e)?,
            Call(e) => self.lower_call(e)?,
            Cond(e) => self.lower_cond(e)?,
            Block(e) => self.lower_block(e)?,
            Index(e) => self.lower_index(e)?,
            e => e, // some expressions don't contain other nodes
        };

        Ok(Node::Expr(expr))
    }

    fn lower_ident(&mut self, expr: ast::Ident) -> ExprResult {
        Ok(Expression::Ident(ast::Ident { name: expr.name, ty: expr.ty }))
    }

    // Lower `x += 1` to `x = x + 1`
    fn lower_binop(&mut self, expr: ast::BinOp) -> ExprResult {
        use Operator::*;

        let orig_lhs = expr.lhs.clone();
        let orig_ty = expr.ty.clone();

        let top_op;
        let rhs = match expr.op {
            AddEq => {
                top_op = Assign;
                Node::Expr(Expression::BinOp(ast::BinOp {
                    op: Add,
                    lhs: expr.lhs,
                    rhs: expr.rhs,
                    ty: expr.ty,
                }))
            },
            SubEq => {
                top_op = Assign;
                Node::Expr(Expression::BinOp(ast::BinOp {
                    op: Sub,
                    lhs: expr.lhs,
                    rhs: expr.rhs,
                    ty: expr.ty,
                }))
            },
            MulEq => {
                top_op = Assign;
                Node::Expr(Expression::BinOp(ast::BinOp {
                    op: Mul,
                    lhs: expr.lhs,
                    rhs: expr.rhs,
                    ty: expr.ty,
                }))
            },
            DivEq => {
                top_op = Assign;
                Node::Expr(Expression::BinOp(ast::BinOp {
                    op: Div,
                    lhs: expr.lhs,
                    rhs: expr.rhs,
                    ty: expr.ty,
                }))
            },
            _ => {
                top_op = expr.op;
                *expr.rhs
            },
        };

        Ok(Expression::BinOp(ast::BinOp {
            op: top_op,
            lhs: Box::new(self.lower_node(*orig_lhs)?),
            rhs: Box::new(self.lower_node(rhs)?),
            ty: orig_ty,
        }))
    }

    fn lower_unop(&mut self, expr: ast::UnOp) -> ExprResult {
        Ok(Expression::UnOp(ast::UnOp {
            op: expr.op,
            rhs: Box::new(self.lower_node(*expr.rhs)?),
            ty: expr.ty,
        }))
    }

    fn lower_call(&mut self, expr: ast::Call) -> ExprResult {
        let sym = self
            .symbol_table
            .get(&expr.name)
            .unwrap_or_else(|| unreachable!("missing symbol in `lower_call()` for `{}`", expr.name));

        // Update the AST with the lowered name if it hasn't been done already and it's
        // not an extern call
        let lowered_name = match sym.name() {
            sym_name if !sym.is_extern() && sym_name != expr.name => sym_name.to_owned(),
            _ => expr.name,
        };

        let mut lowered_args = vec![];
        for node in expr.args {
            lowered_args.push(self.lower_node(node)?);
        }
        Ok(Expression::Call(ast::Call { name: lowered_name, args: lowered_args, ty: expr.ty }))
    }

    fn lower_cond(&mut self, expr: ast::Cond) -> ExprResult {
        Ok(Expression::Cond(ast::Cond {
            cond_expr: Box::new(self.lower_node(*expr.cond_expr)?),
            then_block: Box::new(self.lower_node(*expr.then_block)?),
            else_block: expr.else_block.map(|e| self.lower_node(*e)).transpose()?.map(Box::new),
            ty: expr.ty,
        }))
    }

    fn lower_block(&mut self, expr: ast::Block) -> ExprResult {
        self.symbol_table.enter_scope();

        let mut lowered_list = vec![];
        for node in expr.list {
            lowered_list.push(self.lower_node(node)?);
        }

        self.symbol_table.leave_scope();

        Ok(Expression::Block(ast::Block { list: lowered_list, ty: expr.ty }))
    }

    fn lower_index(&mut self, expr: ast::Index) -> ExprResult {
        Ok(Expression::Index(ast::Index {
            binding: Box::new(self.lower_node(*expr.binding)?),
            idx: Box::new(self.lower_node(*expr.idx)?),
            ty: expr.ty,
        }))
    }

    // Helper for variable initializations
    fn lower_var_init(&mut self, name: &str, init: Option<Box<Node>>) -> Result<Node, String> {
        if let Some(init) = init {
            self.lower_node(*init)
        } else {
            unreachable!("no initializer for variable: `{}`", name);
        }
    }
}
