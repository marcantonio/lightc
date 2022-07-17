use ast::{make_literal, Ast, AstVisitor, Expression, Literal, Node, Prototype, Statement, Visitable};
use common::{Operator, Type};
use common::{ScopeTable, SymbolTable};

#[macro_use]
extern crate common;

mod macros;
#[cfg(test)]
mod tests;

// Current performs the following tasks:
// - applies types to all expressions
// - checks for annotation consistency
// - checks for type consistency and relevance in binops
// - checks for type consistency in for step
// - checks for type consistency in if branches
// - initializes uninitialized variables
// - checks main()'s annotation

type StmtResult = Result<Statement, String>;
type ExprResult = Result<Expression, String>;

pub struct TypeChecker<'a> {
    ast: Ast<Node>,
    scope_table: ScopeTable<Type>,
    symbol_table: &'a mut SymbolTable,
}

impl<'a> AstVisitor for TypeChecker<'a> {
    type Result = Result<Node, String>;

    fn visit_stmt(&mut self, s: Statement) -> Self::Result {
        self.check_stmt(s)
    }

    fn visit_expr(&mut self, e: Expression) -> Self::Result {
        self.check_expr(e, None)
    }
}

impl<'a> TypeChecker<'a> {
    pub fn new(symbol_table: &'a mut SymbolTable) -> Self {
        TypeChecker { ast: Ast::new(), scope_table: ScopeTable::new(), symbol_table }
    }

    pub fn walk(mut self, ast: Ast<Node>) -> Result<Ast<Node>, String> {
        for node in ast.into_nodes() {
            let thir_node = node.accept(&mut self)?;
            self.ast.add(thir_node)
        }
        Ok(self.ast)
    }

    // Helper function for when we don't know if we have a statement or an
    // expression
    fn check_node(&mut self, node: Node, ty: Option<&Type>) -> Result<Node, String> {
        Ok(match node {
            Node::Stmt(s) => self.check_stmt(s)?,
            Node::Expr(e) => self.check_expr(e, ty)?,
        })
    }

    fn check_stmt(&mut self, stmt: Statement) -> Result<Node, String> {
        use Statement::*;

        let stmt = match stmt {
            For { start_name, start_antn, start_expr, cond_expr, step_expr, body } => {
                self.check_for(start_name, start_antn, start_expr, *cond_expr, *step_expr, *body)?
            },
            Let { name, antn, init } => self.check_let(name, antn, init)?,
            Fn { proto, body } => self.check_func(*proto, body)?,
            Struct { attributes, methods, .. } => self.check_struct(attributes, methods)?,
        };

        Ok(Node::Stmt(stmt))
    }

    fn check_for(
        &mut self, start_name: String, start_antn: Type, start_expr: Option<Box<Node>>, cond_expr: Node,
        step_expr: Node, body: Node,
    ) -> StmtResult {
        let start_expr = self.check_var_init(&start_name, start_expr, &start_antn, "for statement")?;

        // Remove old variable. Ignore failure. Insert starting variable.
        let old_var = self.scope_table.remove(&start_name);
        self.scope_table.insert(&start_name, start_antn.clone())?;

        // Ensure the loop cond is always a bool
        let cond_expr = self.check_node(cond_expr, None)?;

        if cond_expr.ty().unwrap_or_default() != Type::Bool {
            return Err("For loop conditional should always be a bool".to_string());
        }

        // Make sure the step type matches the starting variable
        let step_expr = self.check_node(step_expr, Some(&start_antn))?;
        let step_ty = step_expr.ty().unwrap_or_default();
        if step_ty != start_antn {
            return Err(format!(
                "Step type mismatch in for statement. Step is `{}` but `{}` is `{}`",
                step_ty, start_name, start_antn
            ));
        }

        // Check body
        let body_node = self.check_node(body, None)?;

        // Reset shadowed variable if present
        self.scope_table.remove(&start_name);
        if let Some(v) = old_var {
            self.scope_table.insert(&start_name, v)?;
        }

        Ok(Statement::For {
            start_name,
            start_antn,
            start_expr: Some(Box::new(start_expr)),
            cond_expr: Box::new(cond_expr),
            step_expr: Box::new(step_expr),
            body: Box::new(body_node),
        })
    }

    fn check_let(&mut self, name: String, antn: Type, init: Option<Box<Node>>) -> StmtResult {
        let init_node = self.check_var_init(&name, init, &antn, "let statement")?;
        self.scope_table.insert(&name, antn.clone())?;
        Ok(Statement::Let { name, antn, init: Some(Box::new(init_node)) })
    }

    // Check function definitions. This function also does the proto.
    fn check_func(&mut self, mut proto: Prototype, body: Option<Box<Node>>) -> StmtResult {
        let fn_entry = match self.symbol_table.get(proto.name()).cloned() {
            Some(sym) => sym,
            None => unreachable!("Internal error: missing symbol table entry for function: {}", proto.name()),
        };

        // If body is None, this is an extern and no checking is needed
        let body = match body {
            Some(body) => body,
            None => return Ok(Statement::Fn { proto: Box::new(proto), body }),
        };

        // Insert args into the local scope table
        for (name, ty) in proto.args() {
            self.scope_table.insert(name, ty.clone())?;
        }

        let body_node = self.check_node(*body, None)?;
        let body_ty = body_node.ty().unwrap_or_default();

        // Make sure these are in sync since there's no `check_proto()`
        if proto.name() == "main" {
            if proto.ret_ty().is_some() {
                return Err(format!(
                    "main()'s return value shouldn't be annotated. Found `{}`",
                    proto.ret_ty().unwrap()
                ));
            }
            proto.set_ret_ty(Some(&Type::Void));
        } else {
            proto.set_ret_ty(Some(fn_entry.ret_ty()));
        }

        // Make sure function return type and the last statement match. Ignore
        // body type when proto is void.
        if fn_entry.ret_ty() != &body_ty && fn_entry.ret_ty() != &Type::Void && proto.name() != "main" {
            return Err(format!(
                "Function `{}` should return type `{}` but last statement is `{}`",
                proto.name(),
                fn_entry.ret_ty(),
                body_ty
            ));
        }

        // Pop args
        for (name, _) in proto.args() {
            self.scope_table.remove(name);
        }

        Ok(Statement::Fn { proto: Box::new(proto), body: Some(Box::new(body_node)) })
    }

    fn check_struct(&mut self, _attributes: Vec<Node>, _methods: Vec<Node>) -> StmtResult {
        // // Drop scope
        // self.symbol_table.down_scope();

        // for node in attributes {
        //     self.check_node(node)?;
        // }

        // for node in methods {
        //     self.check_node(node)?;
        // }

        // // Pop up 1 level. Drops old scope.
        // self.symbol_table.up_scope()?;

        // Ok(())
        todo!()
    }

    fn check_expr(&mut self, expr: Expression, ty_hint: Option<&Type>) -> Result<Node, String> {
        use Expression::*;

        let expr = match expr {
            Lit { value, .. } => self.check_lit(value, ty_hint)?,
            Ident { name, .. } => self.check_ident(name)?,
            BinOp { op, lhs, rhs, .. } => self.check_binop(op, *lhs, *rhs)?,
            UnOp { op, rhs, .. } => self.check_unop(op, *rhs)?,
            Call { name, args, .. } => self.check_call(name, args)?,
            Cond { cond_expr, then_block, else_block, .. } => {
                self.check_cond(*cond_expr, *then_block, else_block)?
            },
            Block { list, .. } => self.check_block(list)?,
            Index { binding, idx, .. } => self.check_index(*binding, *idx)?,
        };

        Ok(Node::Expr(expr))
    }

    // If there's a type hint, use it or fail. If not, use the literal's
    // type. Update `lit` with the result and return the type.
    fn check_lit(&mut self, lit: Literal, ty_hint: Option<&Type>) -> ExprResult {
        use Literal::*;

        let (new_lit, lit_ty) = match ty_hint {
            Some(hint) => match lit {
                Int8(_) => (lit, Type::Int8),
                Int16(_) => (lit, Type::Int16),
                Int32(_) => (lit, Type::Int32),
                Int64(_) => (lit, Type::Int64),
                UInt8(_) => (lit, Type::UInt8),
                UInt16(_) => (lit, Type::UInt16),
                UInt32(_) => (lit, Type::UInt32),
                UInt64(v) => match hint {
                    Type::Int8 => convert_num!(v, Int8, i8),
                    Type::Int16 => convert_num!(v, Int16, i16),
                    Type::Int32 => convert_num!(v, Int32, i32),
                    Type::Int64 => convert_num!(v, Int64, i64),
                    Type::UInt8 => convert_num!(v, UInt8, u8),
                    Type::UInt16 => convert_num!(v, UInt16, u16),
                    Type::UInt32 => convert_num!(v, UInt32, u32),
                    Type::UInt64 => convert_num!(v, UInt64, u64),
                    float_types!() => return Err("Literal is an integer in a float context".to_string()),
                    Type::Bool => return Err("Literal is an integer in a bool context".to_string()),
                    Type::Char => return Err("Literal is an integer in a char context".to_string()),
                    Type::Array(..) => return Err("Literal is an integer in an array context".to_string()),
                    Type::Void => return Err("Literal is an integer in a void context".to_string()),
                },
                Float(v) => match hint {
                    Type::Float => convert_num!(v, Float, f32),
                    Type::Double => convert_num!(v, Double, f64),
                    int_types!() => return Err("Literal is a float in an integer context".to_string()),
                    Type::Bool => return Err("Literal is a float in a bool context".to_string()),
                    Type::Char => return Err("Literal is a float in a char context".to_string()),
                    Type::Array(..) => return Err("Literal is a float in an array context".to_string()),
                    _ => unreachable!("Internal error: float conversion error"),
                },
                Double(_) => (lit, Type::Double),
                Bool(_) => (lit, Type::Bool),
                Char(_) => (lit, Type::Char),
                Array { .. } => self.check_lit_array(lit, ty_hint)?,
            },
            None => match lit {
                Int32(v) => (Int32(v), Type::Int32), // Only used for main's return value
                UInt64(v) => {
                    let v = i32::try_from(v).map_err(|_| "Numeric literal out of range")?;
                    (Int32(v), Type::Int32)
                },
                Float(_) => (lit, Type::Float),
                Bool(_) => (lit, Type::Bool),
                Char(_) => (lit, Type::Char),
                Array { .. } => self.check_lit_array(lit, ty_hint)?,
                x => unreachable!("Internal error: numeric conversion error for {}", x),
            },
        };

        Ok(Expression::Lit { value: new_lit, ty: Some(lit_ty) })
    }

    fn check_lit_array(&mut self, lit: Literal, ty_hint: Option<&Type>) -> Result<(Literal, Type), String> {
        // Extract the elements vec and the type of the array elements. Will always be None as
        // assigned by the parser as this point.
        let elements = match lit {
            Literal::Array { elements, .. } => elements,
            _ => unreachable!("Internal error: expected array literal"),
        };

        // Clone the inner type hint
        let (ty, size) = match ty_hint.unwrap() {
            Type::Array(ty, sz) => (ty.clone(), sz),
            err => unreachable!("Internal error: array literal has invalid type hint `{}`", err),
        };

        // Make sure array is big enough
        if elements.len() as u32 as usize > *size {
            return Err(format!("Array literal too big in assignment: `{}` > `{}`", elements.len(), size));
        }

        // Check every element and make sure they are uniform
        let mut chkd_elements = Vec::with_capacity(elements.len());
        for el in elements {
            let el_node = self.check_node(el, Some(&ty))?;
            let el_ty = el_node.ty().unwrap_or_default();
            if el_ty != *ty {
                return Err(format!("Array literal's element wrong type: `{}` isn't a `{}`", el_node, ty));
            }
            chkd_elements.push(el_node);
        }

        // Rebuild the literal and return the type
        Ok((Literal::Array { elements: chkd_elements, inner_ty: Some(*ty.clone()) }, Type::Array(ty, *size)))
    }

    fn check_ident(&self, name: String) -> ExprResult {
        let ident_ty = self.scope_table.get(&name).ok_or(format!("Unknown variable: `{}`", name))?;
        Ok(Expression::Ident { name, ty: Some(ident_ty) })
    }

    // TODO: Check overflow on math ops
    fn check_binop(&mut self, op: Operator, lhs: Node, rhs: Node) -> ExprResult {
        use Operator::*;

        // Make sure LHS is a var in assignments
        if op == Assign && !matches!(lhs.as_expr(), Expression::Ident { .. } | Expression::Index { .. }) {
            return Err("Expected LHS to be a variable for assignment".to_string());
        }

        // Check if either side is a numeric literal. If so use the other side
        // as a type hint for the literal type.
        let (chkd_lhs, lhs_ty, chkd_rhs, rhs_ty);
        if lhs.as_expr().is_num_literal() {
            chkd_rhs = self.check_node(rhs, None)?;
            rhs_ty = chkd_rhs.ty().unwrap_or_default();
            chkd_lhs = self.check_node(lhs, Some(&rhs_ty))?;
            lhs_ty = chkd_lhs.ty().unwrap_or_default();
        } else {
            chkd_lhs = self.check_node(lhs, None)?;
            lhs_ty = chkd_lhs.ty().unwrap_or_default();
            chkd_rhs = self.check_node(rhs, Some(&lhs_ty))?;
            rhs_ty = chkd_rhs.ty().unwrap_or_default();
        }

        // Both sides must match
        if lhs_ty != rhs_ty {
            return Err(format!("Mismatched types in binop: `{}` != `{}`", lhs_ty, rhs_ty));
        }

        // Check the operand types based on the operator used and set the
        // expression type accordingly
        let ty = match op {
            And | Or => {
                if lhs_ty != Type::Bool || rhs_ty != Type::Bool {
                    return Err(format!(
                        "Expected bools on either side of `{}`, got lhs: `{}`, rhs: `{}`",
                        op, lhs_ty, rhs_ty
                    ));
                }
                Type::Bool
            },
            Eq | NotEq => {
                match (&lhs_ty, &rhs_ty) {
                    (
                        numeric_types!() | Type::Bool | Type::Char,
                        numeric_types!() | Type::Bool | Type::Char,
                    ) => (),
                    _ => {
                        return Err(format!(
                            "Invalid type combination found in `{}` operation: (lhs: `{}`, rhs: `{}`)",
                            op, lhs_ty, rhs_ty
                        ))
                    },
                };
                Type::Bool
            },
            Gt | GtEq | Lt | LtEq => {
                match (&lhs_ty, &rhs_ty) {
                    (numeric_types!() | Type::Char, numeric_types!() | Type::Char) => (),
                    _ => {
                        return Err(format!(
                            "Invalid type combination found in `{}` operation: (lhs: `{}`, rhs: `{}`)",
                            op, lhs_ty, rhs_ty
                        ))
                    },
                };
                Type::Bool
            },
            Add | Div | Mul | Pow | Sub | BitAnd | BitXor | BitOr => {
                match (&lhs_ty, &rhs_ty) {
                    (numeric_types!(), numeric_types!()) => (),
                    _ => {
                        return Err(format!(
                            "Invalid type combination found in `{}` operation: (lhs: `{}`, rhs: `{}`)",
                            op, lhs_ty, rhs_ty
                        ))
                    },
                };
                lhs_ty.clone()
            },
            _ => Type::Void,
        };

        Ok(Expression::BinOp { op, lhs: Box::new(chkd_lhs), rhs: Box::new(chkd_rhs), ty: Some(ty) })
    }

    fn check_unop(&mut self, op: Operator, rhs: Node) -> ExprResult {
        let chkd_rhs = self.check_node(rhs, None)?;
        let rhs_ty = chkd_rhs.ty().unwrap_or_default();
        match rhs_ty {
            numeric_types!() => (),
            _ => {
                return Err(format!(
                    "Expected numeric type in unary operation `{}`, got rhs: `{}`",
                    op, rhs_ty
                ))
            },
        }
        Ok(Expression::UnOp { op, rhs: Box::new(chkd_rhs), ty: Some(rhs_ty) })
    }

    fn check_call(&mut self, name: String, args: Vec<Node>) -> ExprResult {
        // Pull the function for the call from the table
        let fn_entry =
            self.symbol_table.get(&name).ok_or(format!("Call to undefined function: `{}`", name))?.clone();

        // Pull out the function arg types
        let fe_arg_tys = fn_entry.arg_tys().to_vec();

        // Check arg length
        let fe_args_len = fe_arg_tys.len();
        let args_len = args.len();
        if fe_arg_tys.len() != args.len() {
            return Err(format!("Call to `{}()` takes {} args and {} were given", name, fe_args_len, args_len));
        }

        // Check all args and record their types. Use the function entry arg types as type
        // hints.
        let ret_ty = fn_entry.ret_ty().clone();
        let mut chkd_args = Vec::with_capacity(args_len);
        let mut arg_tys = Vec::with_capacity(args_len);
        for (idx, expr) in args.into_iter().enumerate() {
            let chkd_arg = self.check_node(expr, Some(fe_arg_tys[idx]))?;
            arg_tys.push((idx, chkd_arg.ty().unwrap_or_default().clone()));
            chkd_args.push(chkd_arg);
        }

        // Make sure the function args and the call args jive
        fe_arg_tys.iter().zip(arg_tys).try_for_each(|(fa_ty, (idx, ca_ty))| {
            if *fa_ty != &ca_ty {
                Err(format!("Type mismatch in arg {} of call to `{}()`: `{}` != `{}`", idx + 1, name, fa_ty, ca_ty))
            } else {
                Ok(())
            }
        })?;

        Ok(Expression::Call { name, args: chkd_args, ty: Some(ret_ty) })
    }

    fn check_cond(&mut self, cond_expr: Node, then_block: Node, else_block: Option<Box<Node>>) -> ExprResult {
        let chkd_cond = self.check_node(cond_expr, None)?;
        let cond_ty = chkd_cond.ty().unwrap_or_default();
        if cond_ty != Type::Bool {
            return Err("Conditional should always be a bool".to_string());
        }

        let chkd_then = self.check_node(then_block, None)?;
        let then_ty = chkd_then.ty().unwrap_or_default();

        // Consequent and alternate must match if else exists
        let mut chkd_else = None;
        if let Some(else_block) = else_block {
            let chkd_node = self.check_node(*else_block, Some(&then_ty))?;
            let else_ty = chkd_node.ty().unwrap_or_default();
            chkd_else = Some(Box::new(chkd_node));
            if then_ty != else_ty {
                return Err(format!(
                    "Both arms of conditional must be the same type: `then` == `{}`; `else` == `{}`",
                    then_ty, else_ty
                ));
            }
        }

        Ok(Expression::Cond {
            cond_expr: Box::new(chkd_cond),
            then_block: Box::new(chkd_then),
            else_block: chkd_else,
            ty: Some(then_ty.clone()),
        })
    }

    // Check the block expressions. Ensures statements always eval to void.
    fn check_block(&mut self, list: Vec<Node>) -> ExprResult {
        // Drop scope
        self.scope_table.down_scope();

        // The block type is set to the final node's type
        let mut chkd_list = Vec::with_capacity(list.len());
        let mut list_ty = Type::Void;
        for node in list {
            let chkd_node = self.check_node(node, None)?;
            list_ty = chkd_node.ty().unwrap_or_default().clone();
            chkd_list.push(chkd_node);
        }

        // Pop up 1 level. Drops old scope.
        self.scope_table.up_scope()?;

        Ok(Expression::Block { list: chkd_list, ty: Some(list_ty) })
    }

    fn check_index(&mut self, binding: Node, idx: Node) -> ExprResult {
        let chkd_binding = self.check_node(binding, None)?;
        let binding_ty = match chkd_binding.ty().unwrap_or_default() {
            Type::Array(t, _) => Some((*t).clone()),
            t => return Err(format!("Can't index `{}`", t)),
        };

        // TODO: Coerce into int32
        let chkd_idx = self.check_node(idx, Some(&Type::Int32))?;
        let idx_ty = chkd_idx.ty().unwrap_or_default();
        if !matches!(idx_ty, int_types!()) {
            return Err(format!("Array index must be an `int`, found `{}`", idx_ty));
        } else if !matches!(idx_ty, Type::Int32) {
            return Err("Index must be an int32 (for now)".to_string());
        }

        Ok(Expression::Index { binding: Box::new(chkd_binding), idx: Box::new(chkd_idx), ty: binding_ty })
    }

    // Helper for variable initializations
    fn check_var_init(
        &mut self, name: &str, init: Option<Box<Node>>, antn: &Type, caller: &str,
    ) -> Result<Node, String> {
        use Type::*;

        // If init exists, make sure it matches the variable's annotation
        let init_node = if let Some(init) = init {
            let init_node = self.check_node(*init, Some(antn))?;
            let init_ty = init_node.ty().unwrap_or_default();
            if antn != &init_ty {
                return Err(format!(
                    "Types don't match in {}. `{}` annotated with `{}` but initial value is `{}`",
                    caller, name, antn, init_ty
                ));
            }
            init_node
        } else {
            let literal = match antn {
                Int8 => make_literal!(Int8, 0),
                Int16 => make_literal!(Int16, 0),
                Int32 => make_literal!(Int32, 0),
                Int64 => make_literal!(Int64, 0),
                UInt8 => make_literal!(UInt8, 0),
                UInt16 => make_literal!(UInt16, 0),
                UInt32 => make_literal!(UInt32, 0),
                UInt64 => make_literal!(UInt64, 0),
                Float => make_literal!(Float, 0.0),
                Double => make_literal!(Double, 0.0),
                Char => make_literal!(Char, 0),
                Bool => make_literal!(Bool, false),
                Array(ty, len) => make_literal!(Array, ty.clone(), *len),
                Void => unreachable!("Internal error: void type for variable initialization annotation"),
            };
            Node::new(Node::Expr, literal)
        };
        Ok(init_node)
    }
}
