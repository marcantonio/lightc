use std::collections::HashMap;

use crate::ast::as_expr::AsExprMut;
use crate::ast::*;
use crate::token::Type;

pub(crate) struct TypeChecker {
    function_table: HashMap<String, Type>,
    variable_table: HashMap<String, Type>,
}

impl AstVisitorMut for TypeChecker {
    type Result = Result<(), String>;

    fn visit_stmt(&mut self, s: &mut Statement) -> Self::Result {
        self.stmt_check(s)
    }

    fn visit_expr(&mut self, e: &mut Expression) -> Self::Result {
        self.expr_check(e)?;
        Ok(())
    }
}

impl TypeChecker {
    pub(crate) fn new() -> Self {
        TypeChecker {
            function_table: HashMap::new(),
            variable_table: HashMap::new(),
        }
    }

    pub(crate) fn walk(&mut self, ast: &mut Ast<Node>) -> Result<(), String> {
        for node in ast.nodes_mut() {
            node.accept(self)?;
        }
        Ok(())
    }

    fn stmt_check(&mut self, stmt: &mut Statement) -> Result<(), String> {
        use Statement::*;
        match stmt {
            // Cond { cond, cons, alt } => {
            //     self.cond_codegen(cond.as_expr()?, &*cons.as_expr()?, &alt.as_expr()?)
            // }
            // For {
            //     var_name,
            //     var_type,
            //     start,
            //     cond,
            //     step,
            //     body,
            // } => self.for_codegen(var_name, *var_type, start, cond, step, body),
            Let { name, antn, init } => self.let_check(name, *antn, &mut init.as_expr_mut()?),
            Fn { proto, body } => self.func_check(proto, body),
            _ => todo!("stmt: {:?}", stmt),
        }
    }

    // TODO: Variable shadowing
    fn func_check(
        &mut self,
        proto: &Prototype,
        body: &mut Option<Vec<Node>>,
    ) -> Result<(), String> {
        // First check if this function has already been defined
        let proto_ty = proto.ret_type.unwrap_or_default();
        if self
            .function_table
            .insert(proto.name.to_owned(), proto_ty)
            .is_some()
        {
            return Err(format!("Function `{}` can't be redefined", proto.name));
        }

        // If body is None, this is an extern and no checking is needed
        let body = match body {
            Some(body) => body,
            None => return Ok(()),
        };

        // Insert args
        for (name, ty) in &proto.args {
            self.variable_table.insert(name.to_owned(), *ty);
        }

        let mut body_ty = Type::Void;
        for node in body {
            body_ty = match node {
                Node::Stmt(s) => {
                    self.stmt_check(s)?;
                    Type::Void
                }
                Node::Expr(e) => self.expr_check(e)?,
            }
        }

        // Make sure function return type and the last statement match. Ignore
        // body type when proto is void, for now.
        if proto_ty != body_ty && proto_ty != Type::Void {
            return Err(format!(
                "Function `{}` should return type `{}` but last statement is `{}`",
                proto.name, proto_ty, body_ty
            ));
        }

        // Pop args
        for (name, _) in &proto.args {
            self.variable_table.remove(name);
        }

        Ok(())
    }

    fn let_check(
        &mut self,
        name: &str,
        antn: Type,
        init: &mut Option<&mut Expression>,
    ) -> Result<(), String> {
        if let Some(init) = init {
            let init_ty = self.expr_check(init)?;
            if antn != init_ty {
                return Err(format!(
                    "Types don't match in let statement. Annotated with {} but initial value is {}",
                    antn, init_ty
                ));
            }
        }
        self.variable_table.insert(name.to_owned(), antn);
        Ok(())
    }

    fn expr_check(&mut self, expr: &mut Expression) -> Result<Type, String> {
        use Expression::*;
        println!("EXPR: {:?}", expr);
        let mm = match expr {
            Lit { value, ty } => self.lit_check(value, ty),
            Ident { name, ty } => self.ident_check(name, ty),
            BinOp {
                sym: _,
                lhs,
                rhs,
                ty,
            } => self.binop_check(lhs.as_expr_mut()?, rhs.as_expr_mut()?, ty),
            UnOp { sym: _, rhs, ty } => self.unop_check(rhs.as_expr_mut()?, ty),
            Call { name, args, ty } => self.call_check(name, &mut args.as_expr_mut()?, ty),
        };
        println!("EXPR after: {:?}", expr);
        mm
    }

    fn lit_check(&self, value: &Literal, ty: &mut Option<Type>) -> Result<Type, String> {
        let lit_ty = match value {
            Literal::I64(_) => Type::I64,
            Literal::U64(_) => Type::U64,
            Literal::F64(_) => Type::F64,
        };
        *ty = Some(lit_ty);
        Ok(lit_ty)
    }

    fn ident_check(&self, name: &str, ty: &mut Option<Type>) -> Result<Type, String> {
        let ident_ty = *self
            .variable_table
            .get(name)
            .ok_or(format!("Unknown variable: {}", name))?; // XXX unify with codegen error
        *ty = Some(ident_ty);
        Ok(ident_ty)
    }

    fn call_check(
        &mut self,
        name: &str,
        args: &mut [&mut Expression],
        ty: &mut Option<Type>,
    ) -> Result<Type, String> {
        // Check all args
        for arg in args {
            self.expr_check(arg)?;
        }

        // Pull return type of call from table
        let ret_ty = *self
            .function_table
            .get(name)
            .ok_or(format!("Call to undefined function: `{}`", name))?;

        // Update expression type
        *ty = Some(ret_ty);

        Ok(ret_ty)
    }

    fn binop_check(
        &mut self,
        lhs: &mut Expression,
        rhs: &mut Expression,
        ty: &mut Option<Type>,
    ) -> Result<Type, String> {
        let lhs_ty = self.expr_check(lhs)?;
        let rhs_ty = self.expr_check(rhs)?;

        if lhs_ty != rhs_ty {
            return Err(format!(
                "Mismatched types in binop: `{}` != `{}`",
                lhs_ty, rhs_ty
            ));
        }
        *ty = Some(lhs_ty);

        Ok(lhs_ty)
    }

    fn unop_check(&mut self, rhs: &mut Expression, ty: &mut Option<Type>) -> Result<Type, String> {
        let rhs_ty = self.expr_check(rhs)?;
        *ty = Some(rhs_ty);
        Ok(rhs_ty)
    }
}
