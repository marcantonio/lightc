use ast::{Ast, AstNode, AstVisitor, Visitable};
use common::Operator;
pub use node::{HirNode, NodeKind};
use symbol_table::{Symbol, SymbolTable, Symbolic};

mod node;
#[cfg(test)]
mod tests;

// Performs the following:
// - desugars x += 1 to x = x + 1
// - cooks function names in the AST and symbol table
// - tracks scope (needed?)

type HirResult = Result<HirNode, String>;

pub struct Hir<'a> {
    symbol_table: &'a mut SymbolTable<Symbol>,
}

impl<'a> AstVisitor for Hir<'a> {
    type AstNode = AstNode;
    type Result = Result<HirNode, String>;

    fn visit_for(&mut self, s: ast::For<Self::AstNode>) -> Self::Result {
        self.lower_for(s)
    }

    fn visit_let(&mut self, s: ast::Let<Self::AstNode>) -> Self::Result {
        self.lower_let(s)
    }

    fn visit_fn(&mut self, s: ast::Fn<Self::AstNode>) -> Self::Result {
        self.lower_func(s)
    }

    fn visit_struct(&mut self, s: ast::Struct<Self::AstNode>) -> Self::Result {
        self.lower_struct(s)
    }

    fn visit_lit(&mut self, e: ast::Lit<Self::AstNode>) -> Self::Result {
        self.lower_lit(e)
    }

    fn visit_binop(&mut self, e: ast::BinOp<Self::AstNode>) -> Self::Result {
        self.lower_binop(e)
    }

    fn visit_unop(&mut self, e: ast::UnOp<Self::AstNode>) -> Self::Result {
        self.lower_unop(e)
    }

    fn visit_ident(&mut self, e: ast::Ident) -> Self::Result {
        self.lower_ident(e)
    }

    fn visit_call(&mut self, e: ast::Call<Self::AstNode>) -> Self::Result {
        self.lower_call(e)
    }

    fn visit_cond(&mut self, e: ast::Cond<Self::AstNode>) -> Self::Result {
        self.lower_cond(e)
    }

    fn visit_block(&mut self, e: ast::Block<Self::AstNode>) -> Self::Result {
        self.lower_block(e)
    }

    fn visit_index(&mut self, e: ast::Index<Self::AstNode>) -> Self::Result {
        self.lower_index(e)
    }
}

impl<'a> Hir<'a> {
    pub fn new(symbol_table: &'a mut SymbolTable<Symbol>) -> Self {
        Hir { symbol_table }
    }

    pub fn walk(mut self, ast: Ast<AstNode>) -> Result<Ast<HirNode>, String> {
        let mut hir = Ast::new();
        for node in ast.into_nodes() {
            let lowered_node = node.accept(&mut self)?;
            hir.add(lowered_node)
        }
        Ok(hir)
    }

    // XXX replace with accept()
    fn lower_node(&mut self, node: AstNode) -> Result<HirNode, String> {
        use ast::NodeKind::*;

        Ok(match node.kind {
            For(s) => self.lower_for(s)?,
            Let(s) => self.lower_let(s)?,
            Fn(s) => self.lower_func(s)?,
            Struct(s) => self.lower_struct(s)?,
            Lit(e) => self.lower_lit(e)?,
            Ident(e) => self.lower_ident(e)?,
            BinOp(e) => self.lower_binop(e)?,
            UnOp(e) => self.lower_unop(e)?,
            Call(e) => self.lower_call(e)?,
            Cond(e) => self.lower_cond(e)?,
            Block(e) => self.lower_block(e)?,
            Index(e) => self.lower_index(e)?,
        })
    }

    fn lower_for(&mut self, stmt: ast::For<AstNode>) -> HirResult {
        // Insert start var
        self.symbol_table.enter_scope();
        self.symbol_table.insert(Symbol::new_var(&stmt.start_name, &stmt.start_antn));

        let start_expr = self.lower_var_init(&stmt.start_name, stmt.start_expr.as_deref())?;
        let cond_expr = self.lower_node(*stmt.cond_expr)?;
        let step_expr = self.lower_node(*stmt.step_expr)?;
        let body = self.lower_node(*stmt.body)?;

        self.symbol_table.leave_scope();

        Ok(HirNode::new_for(stmt.start_name, stmt.start_antn, Some(start_expr), cond_expr, step_expr, body))
    }

    fn lower_let(&mut self, stmt: ast::Let<AstNode>) -> HirResult {
        self.symbol_table.insert(Symbol::new_var(&stmt.name, &stmt.antn));
        let init_node = self.lower_var_init(&stmt.name, stmt.init.as_deref())?;
        Ok(HirNode::new_let(stmt.name, stmt.antn, Some(init_node)))
    }

    fn lower_func(&mut self, mut stmt: ast::Fn<AstNode>) -> HirResult {
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
            self.symbol_table.insert(Symbol::new_var(&arg.0, &arg.1));
        }

        let body_node = stmt.body.map(|e| self.lower_node(*e));

        self.symbol_table.leave_scope();

        Ok(HirNode::new_fn(*stmt.proto, body_node.transpose()?))
    }

    fn lower_struct(&mut self, _stmt: ast::Struct<AstNode>) -> HirResult {
        todo!()
    }

    fn lower_lit(&mut self, expr: ast::Lit<AstNode>) -> HirResult {
        use ast::Literal::*;

        // Rewrapping primitives is annoying. Remove for pimitives if we dump AstNode -> HirNode
        let lit = match expr.value {
            Int8(l) => ast::Literal::Int8(l),
            Int16(l) => ast::Literal::Int16(l),
            Int32(l) => ast::Literal::Int32(l),
            Int64(l) => ast::Literal::Int64(l),
            UInt8(l) => ast::Literal::UInt8(l),
            UInt16(l) => ast::Literal::UInt16(l),
            UInt32(l) => ast::Literal::UInt32(l),
            UInt64(l) => ast::Literal::UInt64(l),
            Float(l) => ast::Literal::Float(l),
            Double(l) => ast::Literal::Double(l),
            Bool(l) => ast::Literal::Bool(l),
            Char(l) => ast::Literal::Char(l),
            Array { .. } => self.lower_lit_array(expr.value)?,
        };
        Ok(HirNode::new_lit(lit, expr.ty))
    }

    fn lower_lit_array(&mut self, lit: ast::Literal<AstNode>) -> Result<ast::Literal<HirNode>, String> {
        // Extract the elements vec and the type of the array elements.
        let (elements, ty) = match lit {
            ast::Literal::Array { elements, inner_ty } => (elements, inner_ty),
            _ => unreachable!("expected array literal"),
        };

        // Rewrap every element
        let mut chkd_elements = Vec::with_capacity(elements.len());
        for el in elements {
            chkd_elements.push(self.lower_node(el)?);
        }

        // Rebuild the literal and return the type
        Ok(ast::Literal::Array { elements: chkd_elements, inner_ty: ty })
    }

    fn lower_ident(&mut self, expr: ast::Ident) -> HirResult {
        Ok(HirNode::new_ident(expr.name, expr.ty))
    }

    // Lower `x += 1` to `x = x + 1`
    fn lower_binop(&mut self, expr: ast::BinOp<AstNode>) -> HirResult {
        use Operator::*;

        let lowered_lhs = self.lower_node(*expr.lhs)?;

        let top_op;
        let rhs = match expr.op {
            AddEq => {
                top_op = Assign;
                HirNode::new_binop(Add, lowered_lhs.clone(), self.lower_node(*expr.rhs)?, expr.ty.clone())
            },
            SubEq => {
                top_op = Assign;
                HirNode::new_binop(Sub, lowered_lhs.clone(), self.lower_node(*expr.rhs)?, expr.ty.clone())
            },
            MulEq => {
                top_op = Assign;
                HirNode::new_binop(Mul, lowered_lhs.clone(), self.lower_node(*expr.rhs)?, expr.ty.clone())
            },
            DivEq => {
                top_op = Assign;
                HirNode::new_binop(Div, lowered_lhs.clone(), self.lower_node(*expr.rhs)?, expr.ty.clone())
            },
            _ => {
                top_op = expr.op;
                self.lower_node(*expr.rhs)?
            },
        };

        Ok(HirNode::new_binop(top_op, lowered_lhs, rhs, expr.ty))
    }

    fn lower_unop(&mut self, expr: ast::UnOp<AstNode>) -> HirResult {
        Ok(HirNode::new_unop(expr.op, self.lower_node(*expr.rhs)?, expr.ty))
    }

    fn lower_call(&mut self, expr: ast::Call<AstNode>) -> HirResult {
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
        Ok(HirNode::new_call(lowered_name, lowered_args, expr.ty))
    }

    fn lower_cond(&mut self, expr: ast::Cond<AstNode>) -> HirResult {
        Ok(HirNode::new_cond(
            self.lower_node(*expr.cond_expr)?,
            self.lower_node(*expr.then_block)?,
            expr.else_block.map(|e| self.lower_node(*e)).transpose()?,
            expr.ty,
        ))
    }

    fn lower_block(&mut self, expr: ast::Block<AstNode>) -> HirResult {
        self.symbol_table.enter_scope();

        let mut lowered_list = vec![];
        for node in expr.list {
            lowered_list.push(self.lower_node(node)?);
        }

        self.symbol_table.leave_scope();

        Ok(HirNode::new_block(lowered_list, expr.ty))
    }

    fn lower_index(&mut self, expr: ast::Index<AstNode>) -> HirResult {
        Ok(HirNode::new_index(self.lower_node(*expr.binding)?, self.lower_node(*expr.idx)?, expr.ty))
    }

    // Helper for variable initializations
    fn lower_var_init(&mut self, name: &str, init: Option<&AstNode>) -> HirResult {
        if let Some(init) = init {
            self.lower_node(init.clone())
        } else {
            unreachable!("no initializer for variable: `{}`", name);
        }
    }
}
