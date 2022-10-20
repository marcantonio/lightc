use ast::{Ast, AstNode, AstVisitor, Visitable};
use common::Operator;
pub use node::HirNode;
use symbol_table::{Symbol, SymbolTable, Symbolic};

pub mod node;
#[cfg(test)]
mod tests;

// Performs the following:
// - desugars x += 1 to x = x + 1
// - cooks function names in the AST and symbol table
// - tracks scope (needed?)

pub struct Hir<'a> {
    symbol_table: &'a mut SymbolTable<Symbol>,
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

    fn lower_lit_array(&mut self, lit: ast::Literal<AstNode>) -> Result<ast::Literal<HirNode>, String> {
        // Extract the elements vec and the type of the array elements.
        let (elements, ty) = match lit {
            ast::Literal::Array { elements, inner_ty } => (elements, inner_ty),
            _ => unreachable!("expected array literal"),
        };

        // Rewrap every element
        let mut chkd_elements = Vec::with_capacity(elements.len());
        for el in elements {
            chkd_elements.push(self.visit_node(el)?);
        }

        // Rebuild the literal and return the type
        Ok(ast::Literal::Array { elements: chkd_elements, inner_ty: ty })
    }

    // Helper for variable initializations
    fn lower_var_init(&mut self, name: &str, init: Option<&AstNode>) -> Result<HirNode, String> {
        if let Some(init) = init {
            self.visit_node(init.clone())
        } else {
            unreachable!("no initializer for variable: `{}`", name);
        }
    }
}

impl<'a> AstVisitor for Hir<'a> {
    type Node = AstNode;
    type Result = Result<HirNode, String>;

    fn visit_node(&mut self, node: Self::Node) -> Self::Result {
        node.accept(self)
    }

    fn visit_for(&mut self, stmt: ast::For<Self::Node>) -> Self::Result {
        // Insert start var
        self.symbol_table.enter_scope();
        self.symbol_table.insert(Symbol::new_var(&stmt.start_name, &stmt.start_antn));

        let start_expr = self.lower_var_init(&stmt.start_name, stmt.start_expr.as_deref())?;
        let cond_expr = self.visit_node(*stmt.cond_expr)?;
        let step_expr = self.visit_node(*stmt.step_expr)?;
        let body = self.visit_node(*stmt.body)?;

        self.symbol_table.leave_scope();

        Ok(HirNode::new_for(stmt.start_name, stmt.start_antn, Some(start_expr), cond_expr, step_expr, body))
    }

    fn visit_let(&mut self, stmt: ast::Let<Self::Node>) -> Self::Result {
        self.symbol_table.insert(Symbol::new_var(&stmt.name, &stmt.antn));
        let init_node = self.lower_var_init(&stmt.name, stmt.init.as_deref())?;
        Ok(HirNode::new_let(stmt.name, stmt.antn, Some(init_node)))
    }

    fn visit_fn(&mut self, stmt: ast::Fn<Self::Node>) -> Self::Result {
        let mut proto = *stmt.proto;
        // Insert a duplicate of the symbol. The new one will have the lowered
        // name. Update the AST as well. Skip for externs.
        let sym = self
            .symbol_table
            .get(proto.name())
            .cloned()
            .unwrap_or_else(|| unreachable!("missing symbol in `lower_func()` for `{}`", proto.name()));

        if !sym.is_extern() {
            proto.set_name(sym.name().to_owned());
            self.symbol_table.insert(sym);
        }

        // This creates an interstitial scope for the arguments in the function definition
        // because lower_block() will also create a new scope. Shouldn't be a practical
        // issue.
        self.symbol_table.enter_scope();

        for arg in proto.args() {
            self.symbol_table.insert(Symbol::new_var(&arg.0, &arg.1));
        }

        let body_node = stmt.body.map(|e| self.visit_node(*e));

        self.symbol_table.leave_scope();

        Ok(HirNode::new_fn(proto, body_node.transpose()?))
    }

    fn visit_struct(&mut self, _stmt: ast::Struct<Self::Node>) -> Self::Result {
        todo!()
    }

    fn visit_lit(&mut self, expr: ast::Lit<Self::Node>) -> Self::Result {
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

    fn visit_ident(&mut self, expr: ast::Ident) -> Self::Result {
        Ok(HirNode::new_ident(expr.name, expr.ty))
    }

    // Lower `x += 1` to `x = x + 1`
    fn visit_binop(&mut self, expr: ast::BinOp<Self::Node>) -> Self::Result {
        use Operator::*;

        let lowered_lhs = self.visit_node(*expr.lhs)?;

        let top_op;
        let rhs = match expr.op {
            AddEq => {
                top_op = Assign;
                HirNode::new_binop(Add, lowered_lhs.clone(), self.visit_node(*expr.rhs)?, expr.ty.clone())
            },
            SubEq => {
                top_op = Assign;
                HirNode::new_binop(Sub, lowered_lhs.clone(), self.visit_node(*expr.rhs)?, expr.ty.clone())
            },
            MulEq => {
                top_op = Assign;
                HirNode::new_binop(Mul, lowered_lhs.clone(), self.visit_node(*expr.rhs)?, expr.ty.clone())
            },
            DivEq => {
                top_op = Assign;
                HirNode::new_binop(Div, lowered_lhs.clone(), self.visit_node(*expr.rhs)?, expr.ty.clone())
            },
            _ => {
                top_op = expr.op;
                self.visit_node(*expr.rhs)?
            },
        };

        Ok(HirNode::new_binop(top_op, lowered_lhs, rhs, expr.ty))
    }

    fn visit_unop(&mut self, expr: ast::UnOp<Self::Node>) -> Self::Result {
        Ok(HirNode::new_unop(expr.op, self.visit_node(*expr.rhs)?, expr.ty))
    }

    fn visit_call(&mut self, expr: ast::Call<Self::Node>) -> Self::Result {
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
            lowered_args.push(self.visit_node(node)?);
        }
        Ok(HirNode::new_call(lowered_name, lowered_args, expr.ty))
    }

    fn visit_cond(&mut self, expr: ast::Cond<Self::Node>) -> Self::Result {
        Ok(HirNode::new_cond(
            self.visit_node(*expr.cond_expr)?,
            self.visit_node(*expr.then_block)?,
            expr.else_block.map(|e| self.visit_node(*e)).transpose()?,
            expr.ty,
        ))
    }

    fn visit_index(&mut self, expr: ast::Index<Self::Node>) -> Self::Result {
        Ok(HirNode::new_index(self.visit_node(*expr.binding)?, self.visit_node(*expr.idx)?, expr.ty))
    }

    fn visit_block(&mut self, expr: ast::Block<Self::Node>) -> Self::Result {
        self.symbol_table.enter_scope();

        let mut lowered_list = vec![];
        for node in expr.list {
            lowered_list.push(self.visit_node(node)?);
        }

        self.symbol_table.leave_scope();

        Ok(HirNode::new_block(lowered_list, expr.ty))
    }
}
