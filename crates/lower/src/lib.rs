use common::symbol_table::Symbolic;
use common::{Literal, Operator, Prototype, Symbol, SymbolTable, Type};
pub use hir::Hir;
use parse::ast::{self, Ast, VisitableNode, Visitor};

pub mod hir;
mod macros;
#[cfg(test)]
mod tests;

// Performs the following:
// - builds the HIR
// - desugars x += 1 to x = x + 1
// - cooks function names in the AST and symbol table
// - tracks scope (needed?)
// - initializes uninitialized variables
// - drops field information from structs
// - inserts let statements to support field/method chaining
// - inserts imported functions into the HIR

pub struct Lower<'a> {
    symbol_table: &'a mut SymbolTable<Symbol>,
    struct_methods: Vec<hir::Node>,
    imported_functions: Vec<Symbol>,
    module: String,
}

impl<'a> Lower<'a> {
    pub fn new(module: &str, symbol_table: &'a mut SymbolTable<Symbol>) -> Self {
        Lower { symbol_table, struct_methods: vec![], imported_functions: vec![], module: module.to_owned() }
    }

    pub fn walk(mut self, ast: Ast<ast::Node>) -> Result<Hir<hir::Node>, String> {
        let mut hir = Hir::new();
        let nodes = ast
            .into_nodes()
            .into_iter()
            .map(|node| node.accept(&mut self))
            .collect::<Result<Vec<_>, String>>()?;

        // Add globals nodes to the right place in the HIR
        nodes.into_iter().chain(self.struct_methods).for_each(|node| match node.kind {
            hir::node::Kind::Fn { ref proto, .. } => {
                hir.add_prototype(proto.clone());
                hir.add_node(node);
            },
            hir::node::Kind::Blank => (),
            _ => unreachable!("invalid node kind at global level"),
        });

        // Inject imported functions into the HIR
        for symbol in self.imported_functions {
            hir.add_prototype(Prototype::from(symbol))
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
    fn lower_var_init(
        &mut self, name: &str, init: Option<&ast::Node>, antn: &Type,
    ) -> Result<hir::Node, String> {
        if let Some(init) = init {
            self.visit_node(init.clone())
        } else {
            self.init_null(name, antn)
        }
    }

    fn init_null(&mut self, name: &str, antn: &Type) -> Result<hir::Node, String> {
        use Type::*;

        Ok(match antn {
            Int8 => init_literal!(Int8, 0),
            Int16 => init_literal!(Int16, 0),
            Int32 => init_literal!(Int32, 0),
            Int64 => init_literal!(Int64, 0),
            UInt8 => init_literal!(UInt8, 0),
            UInt16 => init_literal!(UInt16, 0),
            UInt32 => init_literal!(UInt32, 0),
            UInt64 => init_literal!(UInt64, 0),
            Float => init_literal!(Float, 0.0),
            Double => init_literal!(Double, 0.0),
            Char => init_literal!(Char, 0),
            Bool => init_literal!(Bool, false),
            SArray(ty, len) => hir::Node::new_lit(
                Literal::Array { elements: Vec::with_capacity(*len), inner_ty: Some(*ty.clone()) },
                Type::SArray(Box::new(*ty.clone()), *len),
            ),
            Comp(name) => {
                let sym = self
                    .symbol_table
                    .resolve_symbol(name, &self.module)
                    .cloned()
                    .unwrap_or_else(|| unreachable!("missing symbol for `{}` in `init_null()`", name));
                let initializers = if let Some(fields) = sym.fields() {
                    fields
                        .iter()
                        .map(|(n, a)| self.init_null(n, &(*a).into()))
                        .collect::<Result<Vec<_>, String>>()?
                } else {
                    vec![]
                };
                hir::Node::new_lit(Literal::Comp(initializers), Type::Comp(name.to_owned()))
            },
            Void => unreachable!("void type for `{}` variable initialization annotation", name),
        })
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
        self.symbol_table.insert(Symbol::new_var(&start_name, &start_antn, &self.module));

        let start_expr = self.lower_var_init(&start_name, start_expr.as_ref(), &start_antn)?;
        let cond_expr = self.visit_node(cond_expr)?;
        let step_expr = self.visit_node(step_expr)?;
        let body = self.visit_node(body)?;

        self.symbol_table.leave_scope();

        Ok(hir::Node::new_for(start_name, start_antn, Some(start_expr), cond_expr, step_expr, body))
    }

    fn visit_let(&mut self, name: String, antn: Type, init: Option<ast::Node>) -> Self::Result {
        self.symbol_table.insert(Symbol::new_var(&name, &antn, &self.module));
        let init_node = self.lower_var_init(&name, init.as_ref(), &antn)?;
        Ok(hir::Node::new_let(name, antn, Some(init_node)))
    }

    fn visit_fn(&mut self, proto: Prototype, body: Option<ast::Node>) -> Self::Result {
        let mut proto = proto;
        // Insert a duplicate of the symbol. The new one will have the lowered name. Use
        // updated name in the HIR. Skip for externs.
        let sym = self
            .symbol_table
            .get(proto.name())
            .cloned()
            .unwrap_or_else(|| unreachable!("missing symbol in `visit_fn()` for `{}`", proto.name()));

        if !sym.is_extern() {
            // For use in the HIR
            proto.set_name(sym.name().to_owned());
            // Updates the map key name
            self.symbol_table.insert(sym);
        }

        // This creates an interstitial scope for the arguments in the function definition
        // because lower_block() will also create a new scope. Shouldn't be a practical
        // issue.
        self.symbol_table.enter_scope();

        for arg in proto.args() {
            self.symbol_table.insert(Symbol::new_var(&arg.0, &arg.1, &self.module));
        }

        let body_node = body.map(|e| self.visit_node(e));

        self.symbol_table.leave_scope();

        Ok(hir::Node::new_fn(proto, body_node.transpose()?))
    }

    // Structs don't make it into the HIR. The type with fields is already in the symbol
    // table. This lowers the methods to be added via self.struct_methods. Returns a blank
    // node
    fn visit_struct(
        &mut self, _name: String, _fields: Vec<ast::Node>, methods: Vec<ast::Node>,
    ) -> Self::Result {
        // Save the methods separately to pop them up to the top of the HIR later
        let mut lowered_methods =
            methods.into_iter().map(|n| Ok(self.visit_node(n)?)).collect::<Result<Vec<_>, String>>()?;
        self.struct_methods.append(&mut lowered_methods);

        Ok(hir::Node::new_blank())
    }

    fn visit_lit(&mut self, value: Literal<ast::Node>, ty: Option<Type>) -> Self::Result {
        use Literal::*;

        // Rewrapping primitives is annoying. Remove if we dump ast::Node -> hir::Node
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
            Comp(_) => todo!(),
        };
        Ok(hir::Node::new_lit(lit, ty.unwrap_or_default()))
    }

    fn visit_ident(&mut self, name: String, ty: Option<Type>) -> Self::Result {
        Ok(hir::Node::new_ident(name, ty.unwrap_or_default()))
    }

    // Lower `x += 1` to `x = x + 1`
    fn visit_binop(
        &mut self, op: Operator, lhs: ast::Node, rhs: ast::Node, ty: Option<Type>,
    ) -> Self::Result {
        use Operator::*;

        let lowered_lhs = self.visit_node(lhs)?;

        let ty = ty.unwrap_or_default();

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
        Ok(hir::Node::new_unop(op, self.visit_node(rhs)?, ty.unwrap_or_default()))
    }

    fn visit_call(&mut self, name: String, args: Vec<ast::Node>, ty: Option<Type>) -> Self::Result {
        let sym = self
            .symbol_table
            .get(&name)
            .unwrap_or_else(|| unreachable!("missing symbol in `visit_call()` for `{}`", name));

        // Update the HIR with the lowered name if it hasn't been done already and it's
        // not an extern call
        let lowered_name = match sym.name() {
            sym_name if !sym.is_extern() && sym_name != name => sym_name.to_owned(),
            _ => name,
        };

        // Make a list of all imported functions
        if sym.is_import(&self.module) {
            self.imported_functions.push(sym.clone())
        }

        let mut lowered_args = vec![];
        for node in args {
            lowered_args.push(self.visit_node(node)?);
        }
        Ok(hir::Node::new_call(lowered_name, lowered_args, ty.unwrap_or_default()))
    }

    fn visit_cond(
        &mut self, cond_expr: ast::Node, then_block: ast::Node, else_block: Option<ast::Node>,
        ty: Option<Type>,
    ) -> Self::Result {
        Ok(hir::Node::new_cond(
            self.visit_node(cond_expr)?,
            self.visit_node(then_block)?,
            else_block.map(|e| self.visit_node(e)).transpose()?,
            ty.unwrap_or_default(),
        ))
    }

    fn visit_block(&mut self, list: Vec<ast::Node>, ty: Option<Type>) -> Self::Result {
        self.symbol_table.enter_scope();

        let mut lowered_list = vec![];
        for node in list {
            lowered_list.push(self.visit_node(node)?);
        }

        self.symbol_table.leave_scope();

        Ok(hir::Node::new_block(lowered_list, ty.unwrap_or_default()))
    }

    fn visit_index(&mut self, binding: ast::Node, idx: ast::Node, ty: Option<Type>) -> Self::Result {
        Ok(hir::Node::new_index(self.visit_node(binding)?, self.visit_node(idx)?, ty.unwrap_or_default()))
    }

    fn visit_fselector(&mut self, comp: ast::Node, field: String, ty: Option<Type>) -> Self::Result {
        let mut lowered_comp = self.visit_node(comp)?;

        let comp_name = match lowered_comp.ty() {
            Type::Comp(name) => name.to_owned(),
            _ => unreachable!("unexpected type for for field selector target in lower"),
        };

        // If the composite isn't an ident or a let, wrap it in a new let stmt
        if let hir::node::Kind::Call { ty, .. } = lowered_comp.clone().kind {
            lowered_comp = hir::Node::new_let(self.symbol_table.uniq_ident(None), ty, Some(lowered_comp))
        }

        // Find the symbol and extract the index that corresponds to `field`
        let comp_sym = self
            .symbol_table
            .get(&comp_name)
            .unwrap_or_else(|| unreachable!("missing symbol table entry for composite: `{}`", comp_name));
        let idx = comp_sym
            .fields()
            .unwrap_or_default()
            .into_iter()
            .enumerate()
            .find(|(_, f)| f.0 == field)
            .map(|(i, _)| i)
            .unwrap_or_else(|| unreachable!("composite `{}` has no field: `{}`", comp_name, field))
            .try_into()
            .map_err(|err| format!("failed to convert composite index: `{}`", err))?;

        Ok(hir::Node::new_fselector(lowered_comp, idx, ty.unwrap()))
    }

    fn visit_mselector(
        &mut self, comp: ast::Node, name: String, args: Vec<ast::Node>, ty: Option<Type>,
    ) -> Self::Result {
        let lowered_comp = self.visit_node(comp)?;
        let lowered_call = self.visit_call(name, args, ty)?;
        match lowered_call.kind {
            hir::node::Kind::Call { name, mut args, ty } => {
                // Replace `self` ident with the real composite
                args[0] = lowered_comp;
                Ok(hir::Node::new_call(name, args, ty))
            },
            _ => unreachable!("unknown node kind in `visit_mselector()`"),
        }
    }
}
