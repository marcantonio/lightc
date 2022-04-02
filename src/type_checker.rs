use std::collections::HashMap;

use crate::ast::conversion::AsExprMut;
use crate::ast::*;
use crate::token::{Type, Symbol};

pub(crate) struct TypeChecker {
    function_table: HashMap<String, Type>,
    variable_table: HashMap<String, Type>,
}

impl AstVisitorMut for TypeChecker {
    type Result = Result<(), String>;

    fn visit_stmt(&mut self, s: &mut Statement) -> Self::Result {
        self.check_stmt(s)
    }

    fn visit_expr(&mut self, e: &mut Expression) -> Self::Result {
        self.check_expr(e)?;
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

    // Helper function for when we don't know if we have a statement or an
    // expression
    fn check_node(&mut self, node: &mut Node) -> Result<(), String> {
        match node {
            Node::Stmt(s) => self.check_stmt(s),
            Node::Expr(e) => {
                self.check_expr(e)?;
                Ok(())
            }
        }
    }

    fn check_stmt(&mut self, stmt: &mut Statement) -> Result<(), String> {
        use Statement::*;

        match stmt {
            Cond {
                cond_expr,
                then_block,
                else_block,
            } => self.check_cond(cond_expr, then_block, &mut else_block.as_expr_mut()?),
            For {
                start_name,
                start_antn,
                start_expr,
                cond_expr,
                step_expr,
                body,
            } => self.check_for(
                start_name,
                *start_antn,
                start_expr,
                cond_expr,
                step_expr,
                body,
            ),
            Let { name, antn, init } => self.check_let(name, *antn, &mut init.as_expr_mut()?),
            Fn { proto, body } => self.check_func(proto, body),
        }
    }

    // TODO: Variable shadowing
    fn check_func(
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
                    self.check_stmt(s)?;
                    Type::Void
                }
                Node::Expr(e) => self.check_expr(e)?,
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

    fn check_cond(
        &mut self,
        cond_expr: &mut Expression,
        then_block: &mut [Node],
        else_block: &mut Option<Vec<&mut Expression>>,
    ) -> Result<(), String> {
        self.check_expr(cond_expr)?;

        for node in then_block {
            self.check_node(node)?;
        }

        if let Some(else_block) = else_block {
            for expr in else_block {
                self.check_expr(*expr)?;
            }
        }

        Ok(())
    }

    fn check_for(
        &mut self,
        start_name: &str,
        start_antn: Type,
        start_expr: &mut Expression,
        cond_expr: &mut Expression,
        step_expr: &mut Expression,
        body: &mut [Node],
    ) -> Result<(), String> {
        let start_ty = self.check_expr(start_expr)?;
        if start_antn != start_ty {
            return Err(format!(
                "Initial type mismatch in for statement. Annotated with `{}` but value is `{}`",
                start_antn, start_ty
            ));
        }

        // XXX shadowing
        self.variable_table
            .insert(start_name.to_owned(), start_antn);

        // ignore conditional type; it should always be bool
        self.check_expr(cond_expr)?;

        let step_ty = self.check_expr(step_expr)?;
        if step_ty != start_ty {
            return Err(format!(
                "Step type mismatch in for statement. Step is `{}` but `{}` is `{}`",
                step_ty, start_name, start_ty
            ));
        }

        for node in body {
            self.check_node(node)?;
        }

        self.variable_table.remove(start_name);

        Ok(())
    }

    fn check_let(
        &mut self,
        name: &str,
        antn: Type,
        init: &mut Option<&mut Expression>,
    ) -> Result<(), String> {
        if let Some(init) = init {
            let init_ty = self.check_expr(init)?;
            if antn != init_ty {
                return Err(format!(
                    "Types don't match in let statement. Annotated with `{}` but initial value is `{}`",
                    antn, init_ty
                ));
            }
        }
        self.variable_table.insert(name.to_owned(), antn);
        Ok(())
    }

    fn check_expr(&mut self, expr: &mut Expression) -> Result<Type, String> {
        use Expression::*;

        match expr {
            Lit { value, ty } => self.check_lit(value, ty),
            Ident { name, ty } => self.check_ident(name, ty),
            BinOp {
                sym,
                lhs,
                rhs,
                ty,
            } => self.check_binop(*sym, lhs.as_expr_mut()?, rhs.as_expr_mut()?, ty),
            UnOp { sym: _, rhs, ty } => self.check_unop(rhs.as_expr_mut()?, ty),
            Call { name, args, ty } => self.check_call(name, &mut args.as_expr_mut()?, ty),
        }
    }

    fn check_lit(&self, value: &Literal, ty: &mut Option<Type>) -> Result<Type, String> {
        let lit_ty = match value {
            Literal::Int32(_) => Type::Int32,
            Literal::Int64(_) => Type::Int64,
            Literal::UInt32(_) => Type::UInt32,
            Literal::UInt64(_) => Type::UInt64,
            Literal::Float(_) => Type::Float,
            Literal::Double(_) => Type::Double,
        };
        *ty = Some(lit_ty);
        Ok(lit_ty)
    }

    fn check_ident(&self, name: &str, ty: &mut Option<Type>) -> Result<Type, String> {
        let ident_ty = *self
            .variable_table
            .get(name)
            .ok_or(format!("Unknown variable: {}", name))?; // XXX unify with codegen error
        *ty = Some(ident_ty);
        Ok(ident_ty)
    }

    fn check_call(
        &mut self,
        name: &str,
        args: &mut [&mut Expression],
        ty: &mut Option<Type>,
    ) -> Result<Type, String> {
        // Check all args
        for arg in args {
            self.check_expr(arg)?;
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

    fn check_binop(
        &mut self,
        sym: Symbol,
        lhs: &mut Expression,
        rhs: &mut Expression,
        ty: &mut Option<Type>,
    ) -> Result<Type, String> {
        let lhs_ty = self.check_expr(lhs)?;
        let rhs_ty = self.check_expr(rhs)?;

        if lhs_ty != rhs_ty {
            return Err(format!(
                "Mismatched types in binop: `{}` != `{}`",
                lhs_ty, rhs_ty
            ));
        }

        let new_ty = match sym {
            Symbol::And | Symbol::Eq |
            Symbol::Gt |
            Symbol::Lt |
            Symbol::Not |
            Symbol::Or => Type::UInt32,
            _ => lhs_ty,
        };

        *ty = Some(new_ty);

        Ok(new_ty)
    }

    fn check_unop(&mut self, rhs: &mut Expression, ty: &mut Option<Type>) -> Result<Type, String> {
        let rhs_ty = self.check_expr(rhs)?;
        *ty = Some(rhs_ty);
        Ok(rhs_ty)
    }
}
