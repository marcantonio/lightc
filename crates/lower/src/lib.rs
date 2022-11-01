use common::symbol_table::Symbolic;
use common::{Literal, Operator, Prototype, Symbol, SymbolTable, Type};
pub use hir::Hir;
use parse::ast::{self, Ast, VisitableNode, Visitor};

pub mod hir;
#[cfg(test)]
mod tests;

// Performs the following:
// - builds the HIR
// - desugars x += 1 to x = x + 1
// - cooks function names in the AST and symbol table
// - tracks scope (needed?)

pub struct Lower<'a> {
    symbol_table: &'a mut SymbolTable<Symbol>,
}

impl<'a> Lower<'a> {
    pub fn new(symbol_table: &'a mut SymbolTable<Symbol>) -> Self {
        Lower { symbol_table }
    }

    pub fn walk(mut self, ast: Ast<ast::Node>) -> Result<Hir<hir::Node>, String> {
        let mut hir = Hir::new();
        for node in ast.into_nodes() {
            let lowered_node = node.accept(&mut self)?;
            match lowered_node.kind {
                hir::node::Kind::Struct { .. } => hir.add_struct(lowered_node),
                hir::node::Kind::Fn { ref proto, .. } => {
                    hir.add_prototype(proto.clone());
                    hir.add_function(lowered_node);
                },
                _ => unreachable!("invalid node kind at global level"),
            }
        }
        Ok(hir)
    }

    fn lower_lit_array(&mut self, lit: Literal<ast::Node>) -> Result<Literal<hir::Node>, String> {
        // Extract the elements vec and the type of the array elements.
        let (elements, ty) = match lit {
            Literal::Array { elements, inner_ty } => (elements, inner_ty),
            _ => unreachable!("expected array literal"),
        };

        // Rewrap every element
        let mut chkd_elements = Vec::with_capacity(elements.len());
        for el in elements {
            chkd_elements.push(self.visit_node(el)?);
        }

        // Rebuild the literal and return the type
        Ok(Literal::Array { elements: chkd_elements, inner_ty: ty })
    }

    // Helper for variable initializations
    fn lower_var_init(&mut self, name: &str, init: Option<&ast::Node>) -> Result<hir::Node, String> {
        if let Some(init) = init {
            self.visit_node(init.clone())
        } else {
            unreachable!("no initializer for variable: `{}`", name);
        }
    }
}

impl<'a> ast::Visitor for Lower<'a> {
    type AstNode = ast::Node;
    type Result = Result<hir::Node, String>;

    fn visit_node(&mut self, node: Self::AstNode) -> Self::Result {
        node.accept(self)
    }

    fn visit_for(
        &mut self, start_name: String, start_antn: Type, start_expr: Option<ast::Node>, cond_expr: ast::Node,
        step_expr: ast::Node, body: ast::Node,
    ) -> Self::Result {
        // Insert start var
        self.symbol_table.enter_scope();
        self.symbol_table.insert(Symbol::new_var(&start_name, &start_antn));

        let start_expr = self.lower_var_init(&start_name, start_expr.as_ref())?;
        let cond_expr = self.visit_node(cond_expr)?;
        let step_expr = self.visit_node(step_expr)?;
        let body = self.visit_node(body)?;

        self.symbol_table.leave_scope();

        Ok(hir::Node::new_for(start_name, start_antn, Some(start_expr), cond_expr, step_expr, body))
    }

    fn visit_let(&mut self, name: String, antn: Type, init: Option<ast::Node>) -> Self::Result {
        self.symbol_table.insert(Symbol::new_var(&name, &antn));
        let init_node = self.lower_var_init(&name, init.as_ref())?;
        Ok(hir::Node::new_let(name, antn, Some(init_node)))
    }

    fn visit_fn(&mut self, proto: Prototype, body: Option<ast::Node>) -> Self::Result {
        let mut proto = proto;
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

        let body_node = body.map(|e| self.visit_node(e));

        self.symbol_table.leave_scope();

        Ok(hir::Node::new_fn(proto, body_node.transpose()?))
    }

    fn visit_struct(
        &mut self, name: String, fields: Vec<ast::Node>, _methods: Vec<ast::Node>,
    ) -> Self::Result {
        let field_tys = fields
            .into_iter()
            .map(|n| match n.kind {
                ast::node::Kind::Let { antn, .. } => antn,
                _ => unreachable!("invalid node type in struct fields"),
            })
            .collect();
        Ok(hir::Node::new_struct(name, field_tys))
    }

    fn visit_lit(&mut self, value: Literal<ast::Node>, ty: Option<Type>) -> Self::Result {
        use Literal::*;

        // Rewrapping primitives is annoying. Remove for pimitives if we dump ast::Node ->
        // hir::Node
        let lit = match value {
            Int8(l) => Int8(l),
            Int16(l) => Int16(l),
            Int32(l) => Int32(l),
            Int64(l) => Int64(l),
            UInt8(l) => UInt8(l),
            UInt16(l) => UInt16(l),
            UInt32(l) => UInt32(l),
            UInt64(l) => UInt64(l),
            Float(l) => Float(l),
            Double(l) => Double(l),
            Bool(l) => Bool(l),
            Char(l) => Char(l),
            Array { .. } => self.lower_lit_array(value)?,
        };
        Ok(hir::Node::new_lit(lit, ty))
    }

    fn visit_ident(&mut self, name: String, ty: Option<Type>) -> Self::Result {
        Ok(hir::Node::new_ident(name, ty))
    }

    // Lower `x += 1` to `x = x + 1`
    fn visit_binop(
        &mut self, op: Operator, lhs: ast::Node, rhs: ast::Node, ty: Option<Type>,
    ) -> Self::Result {
        use Operator::*;

        let lowered_lhs = self.visit_node(lhs)?;

        let top_op;
        let rhs = match op {
            AddEq => {
                top_op = Assign;
                hir::Node::new_binop(Add, lowered_lhs.clone(), self.visit_node(rhs)?, ty.clone())
            },
            SubEq => {
                top_op = Assign;
                hir::Node::new_binop(Sub, lowered_lhs.clone(), self.visit_node(rhs)?, ty.clone())
            },
            MulEq => {
                top_op = Assign;
                hir::Node::new_binop(Mul, lowered_lhs.clone(), self.visit_node(rhs)?, ty.clone())
            },
            DivEq => {
                top_op = Assign;
                hir::Node::new_binop(Div, lowered_lhs.clone(), self.visit_node(rhs)?, ty.clone())
            },
            _ => {
                top_op = op;
                self.visit_node(rhs)?
            },
        };

        Ok(hir::Node::new_binop(top_op, lowered_lhs, rhs, ty))
    }

    fn visit_unop(&mut self, op: Operator, rhs: ast::Node, ty: Option<Type>) -> Self::Result {
        Ok(hir::Node::new_unop(op, self.visit_node(rhs)?, ty))
    }

    fn visit_call(&mut self, name: String, args: Vec<ast::Node>, ty: Option<Type>) -> Self::Result {
        let sym = self
            .symbol_table
            .get(&name)
            .unwrap_or_else(|| unreachable!("missing symbol in `lower_call()` for `{}`", name));

        // Update the AST with the lowered name if it hasn't been done already and it's
        // not an extern call
        let lowered_name = match sym.name() {
            sym_name if !sym.is_extern() && sym_name != name => sym_name.to_owned(),
            _ => name,
        };

        let mut lowered_args = vec![];
        for node in args {
            lowered_args.push(self.visit_node(node)?);
        }
        Ok(hir::Node::new_call(lowered_name, lowered_args, ty))
    }

    fn visit_cond(
        &mut self, cond_expr: ast::Node, then_block: ast::Node, else_block: Option<ast::Node>,
        ty: Option<Type>,
    ) -> Self::Result {
        Ok(hir::Node::new_cond(
            self.visit_node(cond_expr)?,
            self.visit_node(then_block)?,
            else_block.map(|e| self.visit_node(e)).transpose()?,
            ty,
        ))
    }

    fn visit_block(&mut self, list: Vec<ast::Node>, ty: Option<Type>) -> Self::Result {
        self.symbol_table.enter_scope();

        let mut lowered_list = vec![];
        for node in list {
            lowered_list.push(self.visit_node(node)?);
        }

        self.symbol_table.leave_scope();

        Ok(hir::Node::new_block(lowered_list, ty))
    }

    fn visit_index(&mut self, binding: ast::Node, idx: ast::Node, ty: Option<Type>) -> Self::Result {
        Ok(hir::Node::new_index(self.visit_node(binding)?, self.visit_node(idx)?, ty))
    }
}
