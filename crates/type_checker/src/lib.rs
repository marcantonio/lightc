use ast::{Ast, AstVisitor, Literal, NodeKind, Visitable};
use common::{Operator, Type};
use parser::ParsedNode;
use symbol_table::{Symbol, SymbolTable};
use typed_node::TypedNode;

#[macro_use]
extern crate common;

mod macros;
#[cfg(test)]
mod tests;
mod typed_node;

// Performs the following tasks:
// - applies types to all nodes
// - checks for annotation consistency
// - checks for type consistency and relevance in binops
// - checks for type consistency in for step
// - checks for type consistency in if branches
// - checks main()'s annotation
// - checks for unknown functions and variables
// - initializes uninitialized variables

type TypedResult = Result<TypedNode, String>;

pub struct TypeChecker<'a> {
    ast: Ast<TypedNode>,
    symbol_table: &'a mut SymbolTable<Symbol>,
}

impl<'a> AstVisitor for TypeChecker<'a> {
    type Node = ParsedNode;
    type Result = Result<TypedNode, String>;

    fn visit_for(&mut self, s: ast::For<Self::Node>) -> Self::Result {
        self.check_for(s)
    }

    fn visit_let(&mut self, s: ast::Let<Self::Node>) -> Self::Result {
        self.check_let(s)
    }

    fn visit_fn(&mut self, s: ast::Fn<Self::Node>) -> Self::Result {
        self.check_func(s)
    }

    fn visit_struct(&mut self, s: ast::Struct<Self::Node>) -> Self::Result {
        self.check_struct(s)
    }

    fn visit_lit(&mut self, e: ast::Lit<Self::Node>) -> Self::Result {
        self.check_lit(e, None)
    }

    fn visit_binop(&mut self, e: ast::BinOp<Self::Node>) -> Self::Result {
        self.check_binop(e)
    }

    fn visit_unop(&mut self, e: ast::UnOp<Self::Node>) -> Self::Result {
        self.check_unop(e)
    }

    fn visit_ident(&mut self, e: ast::Ident) -> Self::Result {
        self.check_ident(e)
    }

    fn visit_call(&mut self, e: ast::Call<Self::Node>) -> Self::Result {
        self.check_call(e)
    }

    fn visit_cond(&mut self, e: ast::Cond<Self::Node>) -> Self::Result {
        self.check_cond(e)
    }

    fn visit_block(&mut self, e: ast::Block<Self::Node>) -> Self::Result {
        self.check_block(e)
    }

    fn visit_index(&mut self, e: ast::Index<Self::Node>) -> Self::Result {
        self.check_index(e)
    }
}

impl<'a> TypeChecker<'a> {
    pub fn new(symbol_table: &'a mut SymbolTable<Symbol>) -> Self {
        TypeChecker { ast: Ast::new(), symbol_table }
    }

    pub fn walk(mut self, ast: Ast<ParsedNode>) -> Result<Ast<TypedNode>, String> {
        for node in ast.into_nodes() {
            let typed_node = node.accept(&mut self)?;
            self.ast.add(typed_node)
        }
        Ok(self.ast)
    }

    // Helper function for when we don't know if we have a statement or an
    // expression
    fn check_node(&mut self, node: ParsedNode, ty_hint: Option<&Type>) -> Result<TypedNode, String> {
        use NodeKind::*;

        Ok(match node.node {
            For(s) => self.check_for(s)?,
            Let(s) => self.check_let(s)?,
            Fn(s) => self.check_func(s)?,
            Struct(s) => self.check_struct(s)?,
            Lit(e) => self.check_lit(e, ty_hint)?,
            Ident(e) => self.check_ident(e)?,
            BinOp(e) => self.check_binop(e)?,
            UnOp(e) => self.check_unop(e)?,
            Call(e) => self.check_call(e)?,
            Cond(e) => self.check_cond(e)?,
            Block(e) => self.check_block(e)?,
            Index(e) => self.check_index(e)?,
        })
    }

    fn check_for(&mut self, stmt: ast::For<ParsedNode>) -> TypedResult {
        let start_expr = self.check_var_init(
            &stmt.start_name,
            stmt.start_expr,
            &stmt.start_antn,
            "for statement",
        )?;

        // Insert starting variable
        self.symbol_table.enter_scope();
        self.symbol_table.insert(Symbol::new_var(stmt.start_name.as_str(), &stmt.start_antn));

        // Ensure the loop cond is always a bool
        let cond_expr = self.check_node(*stmt.cond_expr, None)?;

        if cond_expr.ty().unwrap_or_default() != &Type::Bool {
            return Err("For loop conditional should always be a bool".to_string());
        }

        // Make sure the step type matches the starting variable
        let step_expr = self.check_node(*stmt.step_expr, Some(&stmt.start_antn))?;
        let step_ty = step_expr.ty().unwrap_or_default();
        if step_ty != &stmt.start_antn {
            return Err(format!(
                "Step type mismatch in for statement. Step is `{}` but `{}` is `{}`",
                step_ty, stmt.start_name, stmt.start_antn
            ));
        }

        // Check body
        let body_node = self.check_node(*stmt.body, None)?;

        self.symbol_table.leave_scope();

        Ok(TypedNode {
            node: NodeKind::For(ast::For {
                start_name: stmt.start_name,
                start_antn: stmt.start_antn,
                start_expr: Some(Box::new(start_expr)),
                cond_expr: Box::new(cond_expr),
                step_expr: Box::new(step_expr),
                body: Box::new(body_node),
            }),
            ty: None,
        })
    }

    fn check_let(&mut self, stmt: ast::Let<ParsedNode>) -> TypedResult {
        self.symbol_table.insert(Symbol::new_var(stmt.name.as_str(), &stmt.antn));
        let init_node = self.check_var_init(&stmt.name, stmt.init, &stmt.antn, "let statement")?;
        Ok(TypedNode {
            node: NodeKind::Let(ast::Let {
                name: stmt.name,
                antn: stmt.antn,
                init: Some(Box::new(init_node)),
            }),
            ty: None,
        })
    }

    // Check function definitions. This function also does the proto.
    fn check_func(&mut self, mut stmt: ast::Fn<ParsedNode>) -> TypedResult {
        let fn_entry = match self.symbol_table.get(stmt.proto.name()).cloned() {
            Some(sym) => sym,
            None => unreachable!("missing symbol table entry for function: {}", stmt.proto.name()),
        };

        // If body is None, this is an extern and no checking is needed
        let body = match stmt.body {
            Some(body) => body,
            None => {
                return Ok(TypedNode {
                    node: NodeKind::Fn(ast::Fn { proto: stmt.proto, body: None }),
                    ty: None,
                })
            },
        };

        // Creates interstitial scope for the arguments in the function definition
        self.symbol_table.enter_scope();

        // Insert args into the local scope table
        for arg in stmt.proto.args() {
            self.symbol_table.insert(Symbol::new_var(&arg.0, &arg.1));
        }

        let body_node = self.check_node(*body, None)?;
        let body_ty = body_node.ty().unwrap_or_default();

        // Make sure these are in sync since there's no `check_proto()`
        if stmt.proto.name() == "main" {
            if stmt.proto.ret_ty() != &Type::Void {
                return Err(format!(
                    "main()'s return value shouldn't be annotated. Found `{}`",
                    stmt.proto.ret_ty()
                ));
            }
            stmt.proto.set_ret_ty(Type::Void);
        } else {
            stmt.proto.set_ret_ty(fn_entry.ret_ty().to_owned());
        }

        // Make sure function return type and the last statement match. Ignore
        // body type when proto is void.
        if fn_entry.ret_ty() != body_ty
            && fn_entry.ret_ty() != &Type::Void
            && stmt.proto.name() != "main"
        {
            return Err(format!(
                "Function `{}` should return type `{}` but last statement is `{}`",
                stmt.proto.name(),
                fn_entry.ret_ty(),
                body_ty
            ));
        }

        self.symbol_table.leave_scope();

        Ok(TypedNode {
            node: NodeKind::Fn(ast::Fn { proto: stmt.proto, body: Some(Box::new(body_node)) }),
            ty: None,
        })
    }

    fn check_struct(&mut self, stmt: ast::Struct<ParsedNode>) -> TypedResult {
        let mut chkd_fields = vec![];
        for node in stmt.fields {
            chkd_fields.push(self.check_node(node, None)?);
        }

        let mut chkd_methods = vec![];
        for node in stmt.methods {
            chkd_methods.push(self.check_node(node, None)?);
        }

        Ok(TypedNode {
            node: NodeKind::Struct(ast::Struct {
                name: stmt.name,
                fields: chkd_fields,
                methods: chkd_methods,
            }),
            ty: None,
        })
    }

    // If there's a type hint, use it or fail. If not, use the literal's
    // type. Update `lit` with the result and return the type.
    fn check_lit(&mut self, expr: ast::Lit<ParsedNode>, ty_hint: Option<&Type>) -> TypedResult {
        use Literal::*;

        // TODO: Clean this up
        let lit = expr.value;
        let (new_lit, lit_ty): (Literal<TypedNode>, Type) = match ty_hint {
            Some(hint) => match lit {
                Int8(v) => (Int8(v), Type::Int8),
                Int16(v) => (Int16(v), Type::Int16),
                Int32(v) => (Int32(v), Type::Int32),
                Int64(v) => (Int64(v), Type::Int64),
                UInt8(v) => (UInt8(v), Type::UInt8),
                UInt16(v) => (UInt16(v), Type::UInt16),
                UInt32(v) => (UInt32(v), Type::UInt32),
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
                    Type::Comp(_) => return Err("Literal is an integer in a compound context".to_string()),
                },
                Float(v) => match hint {
                    Type::Float => convert_num!(v, Float, f32),
                    Type::Double => convert_num!(v, Double, f64),
                    int_types!() => return Err("Literal is a float in an integer context".to_string()),
                    Type::Bool => return Err("Literal is a float in a bool context".to_string()),
                    Type::Char => return Err("Literal is a float in a char context".to_string()),
                    Type::Array(..) => return Err("Literal is a float in an array context".to_string()),
                    _ => unreachable!("float conversion error"),
                },
                Double(v) => (Double(v), Type::Double),
                Bool(v) => (Bool(v), Type::Bool),
                Char(v) => (Char(v), Type::Char),
                Array { .. } => self.check_lit_array(lit, Some(hint))?,
            },
            None => match lit {
                Int32(v) => (Int32(v), Type::Int32), // Only used for main's return value
                UInt64(v) => {
                    let v = i32::try_from(v).map_err(|_| "Numeric literal out of range")?;
                    (Int32(v), Type::Int32)
                },
                Float(v) => (Float(v), Type::Float),
                Bool(v) => (Bool(v), Type::Bool),
                Char(v) => (Char(v), Type::Char),
                Array { .. } => self.check_lit_array(lit, None)?,
                x => unreachable!("numeric conversion error for {}", x),
            },
        };

        Ok(TypedNode { node: NodeKind::Lit(ast::Lit { value: new_lit }), ty: Some(lit_ty) })
    }

    fn check_lit_array(
        &mut self, lit: Literal<ParsedNode>, ty_hint: Option<&Type>,
    ) -> Result<(Literal<TypedNode>, Type), String> {
        // Extract the elements vec and the type of the array elements. Will always be None as
        // assigned by the parser as this point.
        let elements = match lit {
            Literal::Array { elements, .. } => elements,
            _ => unreachable!("expected array literal"),
        };

        // Clone the inner type hint
        // XXX: Could ty_hint be None?
        let (ty, size) = match ty_hint.unwrap() {
            Type::Array(ty, sz) => (ty.clone(), sz),
            err => unreachable!("array literal has invalid type hint `{}`", err),
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
            if el_ty != ty.as_ref() {
                return Err(format!("Array literal's element wrong type: `{}` isn't a `{}`", el_node, ty));
            }
            chkd_elements.push(el_node);
        }

        // Rebuild the literal and return the type
        Ok((Literal::Array { elements: chkd_elements, inner_ty: Some(*ty.clone()) }, Type::Array(ty, *size)))
    }

    fn check_ident(&self, i: ast::Ident) -> TypedResult {
        let ident_ty =
            self.symbol_table.get(&i.name).ok_or(format!("Unknown variable: `{}`", i.name))?.ty().clone();
        Ok(TypedNode { node: NodeKind::Ident(ast::Ident { name: i.name }), ty: Some(ident_ty) })
    }

    // TODO: Check overflow on math ops
    fn check_binop(&mut self, expr: ast::BinOp<ParsedNode>) -> TypedResult {
        use Operator::*;

        // Make sure LHS is a var in assignments
        if expr.op == Assign
            && !matches!(
                *expr.lhs,
                ParsedNode { node: NodeKind::Ident { .. } } | ParsedNode { node: NodeKind::Index { .. } }
            )
        {
            return Err("Expected LHS to be a variable for assignment".to_string());
        }

        // Check if either side is a numeric literal. If so use the other side
        // as a type hint for the literal type.
        let (chkd_lhs, lhs_ty, chkd_rhs, rhs_ty);
        if expr.lhs.is_num_literal() {
            chkd_rhs = self.check_node(*expr.rhs, None)?;
            rhs_ty = chkd_rhs.ty().unwrap_or_default();
            chkd_lhs = self.check_node(*expr.lhs, Some(rhs_ty))?;
            lhs_ty = chkd_lhs.ty().unwrap_or_default();
        } else {
            chkd_lhs = self.check_node(*expr.lhs, None)?;
            lhs_ty = chkd_lhs.ty().unwrap_or_default();
            chkd_rhs = self.check_node(*expr.rhs, Some(lhs_ty))?;
            rhs_ty = chkd_rhs.ty().unwrap_or_default();
        }

        // Both sides must match
        if lhs_ty != rhs_ty {
            return Err(format!("Mismatched types in binop: `{}` != `{}`", lhs_ty, rhs_ty));
        }

        // Check the operand types based on the operator used and set the
        // expression type accordingly
        let ty = match expr.op {
            And | Or => {
                if lhs_ty != &Type::Bool || rhs_ty != &Type::Bool {
                    return Err(format!(
                        "Expected bools on either side of `{}`, got lhs: `{}`, rhs: `{}`",
                        expr.op, lhs_ty, rhs_ty
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
                            expr.op, lhs_ty, rhs_ty
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
                            expr.op, lhs_ty, rhs_ty
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
                            expr.op, lhs_ty, rhs_ty
                        ))
                    },
                };
                lhs_ty.clone()
            },
            _ => Type::Void,
        };

        Ok(TypedNode {
            node: NodeKind::BinOp(ast::BinOp {
                op: expr.op,
                lhs: Box::new(chkd_lhs),
                rhs: Box::new(chkd_rhs),
            }),
            ty: Some(ty),
        })
    }

    fn check_unop(&mut self, expr: ast::UnOp<ParsedNode>) -> TypedResult {
        let chkd_rhs = self.check_node(*expr.rhs, None)?;
        let rhs_ty = chkd_rhs.ty().cloned().unwrap_or_default();
        match rhs_ty {
            numeric_types!() => (),
            _ => {
                return Err(format!(
                    "Expected numeric type in unary operation `{}`, got rhs: `{}`",
                    expr.op, rhs_ty
                ))
            },
        }
        Ok(TypedNode {
            node: NodeKind::UnOp(ast::UnOp { op: expr.op, rhs: Box::new(chkd_rhs) }),
            ty: Some(rhs_ty),
        })
    }

    fn check_call(&mut self, expr: ast::Call<ParsedNode>) -> TypedResult {
        // Pull the function for the call from the table
        let fn_entry = self
            .symbol_table
            .get(&expr.name)
            .ok_or(format!("Call to undefined function: `{}`", expr.name))?
            .clone();

        // Pull out the function arg types
        let fe_arg_tys = fn_entry.arg_tys().to_vec();

        // Check arg length
        let fe_args_len = fe_arg_tys.len();
        let args_len = expr.args.len();
        if fe_arg_tys.len() != expr.args.len() {
            return Err(format!(
                "Call to `{}()` takes {} args and {} were given",
                expr.name, fe_args_len, args_len
            ));
        }

        // Check all args and record their types. Use the function entry arg types as type
        // hints.
        let ret_ty = fn_entry.ret_ty();
        let mut chkd_args = Vec::with_capacity(args_len);
        let mut arg_tys = Vec::with_capacity(args_len);
        for (idx, expr) in expr.args.into_iter().enumerate() {
            let chkd_arg = self.check_node(expr, Some(&fe_arg_tys[idx]))?;
            arg_tys.push((idx, chkd_arg.ty().unwrap_or_default().clone()));
            chkd_args.push(chkd_arg);
        }

        // Make sure the function args and the call args jive
        fe_arg_tys.iter().zip(arg_tys).try_for_each(|(fa_ty, (idx, ca_ty))| {
            if *fa_ty != &ca_ty {
                Err(format!(
                    "Type mismatch in arg {} of call to `{}()`: `{}` != `{}`",
                    idx + 1,
                    expr.name,
                    fa_ty,
                    ca_ty
                ))
            } else {
                Ok(())
            }
        })?;

        Ok(TypedNode {
            node: NodeKind::Call(ast::Call { name: expr.name, args: chkd_args }),
            ty: Some(ret_ty.clone()),
        })
    }

    fn check_cond(&mut self, expr: ast::Cond<ParsedNode>) -> TypedResult {
        let chkd_cond = self.check_node(*expr.cond_expr, None)?;
        let cond_ty = chkd_cond.ty().unwrap_or_default();
        if cond_ty != &Type::Bool {
            return Err("Conditional should always be a bool".to_string());
        }

        let chkd_then = self.check_node(*expr.then_block, None)?;
        let then_ty = chkd_then.ty().cloned().unwrap_or_default();

        // Consequent and alternate must match if else exists
        let mut chkd_else = None;
        if let Some(else_block) = expr.else_block {
            let chkd_node = self.check_node(*else_block, Some(&then_ty))?;
            let else_ty = chkd_node.ty().cloned().unwrap_or_default();
            chkd_else = Some(Box::new(chkd_node));
            if then_ty != else_ty {
                return Err(format!(
                    "Both arms of conditional must be the same type: `then` == `{}`; `else` == `{}`",
                    then_ty, else_ty
                ));
            }
        }

        Ok(TypedNode {
            node: NodeKind::Cond(ast::Cond {
                cond_expr: Box::new(chkd_cond),
                then_block: Box::new(chkd_then),
                else_block: chkd_else,
            }),
            ty: Some(then_ty),
        })
    }

    // Check the block expressions. Ensures statements always eval to void.
    fn check_block(&mut self, expr: ast::Block<ParsedNode>) -> TypedResult {
        self.symbol_table.enter_scope();

        // The block type is set to the final node's type
        let mut chkd_list = Vec::with_capacity(expr.list.len());
        let mut list_ty = Type::Void;
        for node in expr.list {
            let chkd_node = self.check_node(node, None)?;
            list_ty = chkd_node.ty().unwrap_or_default().clone();
            chkd_list.push(chkd_node);
        }

        self.symbol_table.leave_scope();

        Ok(TypedNode { node: NodeKind::Block(ast::Block { list: chkd_list }), ty: Some(list_ty) })
    }

    fn check_index(&mut self, expr: ast::Index<ParsedNode>) -> TypedResult {
        let chkd_binding = self.check_node(*expr.binding, None)?;
        let binding_ty = match chkd_binding.ty().unwrap_or_default() {
            Type::Array(t, _) => *t.clone(),
            t => return Err(format!("Can't index `{}`", t)),
        };

        // TODO: Coerce into int32
        let chkd_idx = self.check_node(*expr.idx, Some(&Type::Int32))?;
        let idx_ty = chkd_idx.ty().unwrap_or_default();
        if !matches!(idx_ty, int_types!()) {
            return Err(format!("Array index must be an `int`, found `{}`", idx_ty));
        } else if !matches!(idx_ty, Type::Int32) {
            return Err("Index must be an int32 (for now)".to_string());
        }

        Ok(TypedNode {
            node: NodeKind::Index(ast::Index { binding: Box::new(chkd_binding), idx: Box::new(chkd_idx) }),
            ty: Some(binding_ty),
        })
    }

    // Helper for variable initializations
    fn check_var_init(
        &mut self, name: &str, init: Option<Box<ParsedNode>>, antn: &Type, caller: &str,
    ) -> TypedResult {
        use Type::*;

        // If init exists, make sure it matches the variable's annotation
        if let Some(init) = init {
            let init_node = self.check_node(*init, Some(&antn))?;
            let init_ty = init_node.ty().unwrap_or_default();
            if antn != init_ty {
                return Err(format!(
                    "Types don't match in {}. `{}` annotated with `{}` but initial value is `{}`",
                    caller, name, antn, init_ty
                ));
            }
            Ok(init_node)
        } else {
            Ok(match antn {
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
                Array(ty, len) => make_literal!(Array, *ty, *len),
                Void => unreachable!("void type for variable initialization annotation"),
                Comp(_) => todo!(),
            })
        }
    }
}
