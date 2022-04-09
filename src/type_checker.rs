use std::collections::HashMap;

use crate::ast::conversion::AsExprMut;
use crate::ast::*;
use crate::token::{Symbol, Type};

macro_rules! convert_num {
    ($lit:expr, $val:expr, $variant:ident, $ty:ty) => {{
        let v = <$ty>::try_from(*$val).map_err(|_| "Numeric literal out of range")?;
        *$lit = Literal::$variant(v);
        Type::$variant
    }};
}

// Current performs the following tasks:
// - applies types to all expressions
// - checks for annotation consistency
// - checks for type consistency in binops
// - checks for type consistency in for step
// - checks for type consistency in if branches
// - ensures functions aren't redefined
// - cooks main's return value

#[derive(Clone)]
struct FunctionEntry {
    ret_ty: Type,
    arg_tys: Vec<Type>,
}

pub(crate) struct TypeChecker {
    function_table: HashMap<String, FunctionEntry>,
    variable_table: HashMap<String, Type>,
}

impl AstVisitorMut for TypeChecker {
    type Result = Result<(), String>;

    fn visit_stmt(&mut self, s: &mut Statement) -> Self::Result {
        self.check_stmt(s)
    }

    fn visit_expr(&mut self, e: &mut Expression) -> Self::Result {
        self.check_expr(e, None)?;
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
    fn check_node(&mut self, node: &mut Node) -> Result<Type, String> {
        Ok(match node {
            Node::Stmt(s) => {
                self.check_stmt(s)?;
                Type::Void
            }
            Node::Expr(e) => self.check_expr(e, None)?,
        })
    }

    fn check_stmt(&mut self, stmt: &mut Statement) -> Result<(), String> {
        use Statement::*;

        match stmt {
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
        proto: &mut Prototype,
        body: &mut Option<Vec<Node>>,
    ) -> Result<(), String> {
        let mut func_entry = FunctionEntry {
            ret_ty: proto.ret_ty.unwrap_or(Type::Void),
            arg_tys: proto.args.iter().map(|&(_, ty)| ty).collect::<Vec<Type>>(),
        };

        // Check if this function has already been defined and then update the
        // function table
        if self
            .function_table
            .insert(proto.name.to_owned(), func_entry.clone())
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

        // Check the body
        let mut body_ty = Type::Void;
        for node in body.iter_mut() {
            body_ty = match node {
                Node::Stmt(s) => {
                    self.check_stmt(s)?;
                    Type::Void
                }
                Node::Expr(e) => self.check_expr(e, None)?,
            }
        }

        // Ensure main always returns a 0 if nothing is specified
        //
        // TODO: Should go into a desugar phase
        let ret_ty = func_entry.ret_ty;
        if proto.name == "main" && body_ty == Type::Void {
            body.push(Node::Expr(Expression::Lit {
                value: Literal::Int32(0),
                ty: Some(Type::Int32),
            }));
            body_ty = Type::Int32;
            func_entry.ret_ty = body_ty;
            proto.ret_ty = Some(body_ty);
            self.function_table
                .insert(proto.name.to_owned(), func_entry);
        }

        // Make sure function return type and the last statement match. Ignore
        // body type when proto is void, for now.
        if ret_ty != body_ty && ret_ty != Type::Void {
            return Err(format!(
                "Function `{}` should return type `{}` but last statement is `{}`",
                proto.name, ret_ty, body_ty
            ));
        }

        // Pop args
        for (name, _) in &proto.args {
            self.variable_table.remove(name);
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
        let start_ty = self.check_expr(start_expr, None)?;
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
        self.check_expr(cond_expr, None)?;

        let step_ty = self.check_expr(step_expr, None)?;
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
            let init_ty = self.check_expr(init, Some(antn))?;
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

    fn check_expr(&mut self, expr: &mut Expression, ty_hint: Option<Type>) -> Result<Type, String> {
        use Expression::*;

        match expr {
            Lit { value, ty } => self.check_lit(value, ty, ty_hint),
            Ident { name, ty } => self.check_ident(name, ty),
            BinOp { sym, lhs, rhs, ty } => {
                self.check_binop(*sym, lhs.as_expr_mut()?, rhs.as_expr_mut()?, ty)
            }
            UnOp { sym: _, rhs, ty } => self.check_unop(rhs.as_expr_mut()?, ty),
            Call { name, args, ty } => self.check_call(name, &mut args.as_expr_mut()?, ty),
            Cond {
                cond_expr,
                then_block,
                else_block,
                ty,
            } => self.check_cond(cond_expr, then_block, &mut else_block.as_expr_mut()?, ty),
        }
    }

    fn check_lit(
        &self,
        lit: &mut Literal,
        ty: &mut Option<Type>,
        ty_hint: Option<Type>,
    ) -> Result<Type, String> {
        use Literal::*;

        let lit_ty = match ty_hint {
            Some(hint) => match lit {
                // XXX: will we ever hit these?
                Int8(_) => Type::Int8,
                Int16(_) => Type::Int16,
                Int32(_) => Type::Int32,
                Int64(_) => Type::Int64,
                UInt8(_) => Type::UInt8,
                UInt16(_) => Type::UInt16,
                UInt32(_) => Type::UInt32,
                UInt64(v) => match hint {
                    Type::Int8 => convert_num!(lit, v, Int8, i8),
                    Type::Int16 => convert_num!(lit, v, Int16, i16),
                    Type::Int32 => convert_num!(lit, v, Int32, i32),
                    Type::Int64 => convert_num!(lit, v, Int64, i64),
                    Type::UInt8 => convert_num!(lit, v, UInt8, u8),
                    Type::UInt16 => convert_num!(lit, v, UInt16, u16),
                    Type::UInt32 => convert_num!(lit, v, UInt32, u32),
                    Type::UInt64 => convert_num!(lit, v, UInt64, u64),
                    _ => return Err("NONCANBE: Internal integer conversion error".to_string()),
                },
                Float(v) => match hint {
                    Type::Float => convert_num!(lit, v, Float, f32),
                    Type::Double => convert_num!(lit, v, Double, f64),
                    _ => return Err("NONCANBE: Internal float conversion error".to_string()),
                },
                Double(_) => Type::Double,
                Bool(_) => Type::Bool,
            },
            None => match lit {
                UInt64(v) => {
                    let v = i32::try_from(*v).map_err(|_| "Numeric literal out of range")?;
                    *lit = Int32(v);
                    Type::Int32
                }
                Float(_) => Type::Float,
                Bool(_) => Type::Bool,
                x => return Err(format!("NONCANBE: Internal numeric conversion error for {}", x)),
            },
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
        // Pull the function for the call from table
        let func_entry = self
            .function_table
            .get(name)
            .ok_or(format!("Call to undefined function: `{}`", name))?;

        // Pull out the function arg types
        let fe_arg_tys: Vec<Type> = func_entry.arg_tys.to_vec();

        // Update expression type
        let ret_ty = func_entry.ret_ty;
        *ty = Some(ret_ty);

        // Check all args and record their types. Use the function entry arg
        // types as type hints.
        let mut arg_tys = Vec::with_capacity(args.len());
        for (idx, expr) in args.iter_mut().enumerate() {
            arg_tys.push((idx, self.check_expr(*expr, Some(fe_arg_tys[idx]))?));
        }

        // Make sure the function args and the call args jive
        fe_arg_tys
            .iter()
            .zip(arg_tys)
            .try_for_each(|(&fa_ty, (idx, ca_ty))| {
                if fa_ty != ca_ty {
                    Err(format!(
                        "Type mismatch in arg {} of call to {}: {} != {}",
                        idx + 1,
                        name,
                        fa_ty,
                        ca_ty
                    ))
                } else {
                    Ok(())
                }
            })?;

        Ok(ret_ty)
    }

    fn check_binop(
        &mut self,
        sym: Symbol,
        lhs: &mut Expression,
        rhs: &mut Expression,
        ty: &mut Option<Type>,
    ) -> Result<Type, String> {
        let lhs_ty;
        let rhs_ty;

        match (lhs.is_num_literal(), rhs.is_num_literal()) {
            (true, false) => {
                rhs_ty = self.check_expr(rhs, None)?;
                lhs_ty = self.check_expr(lhs, Some(rhs_ty))?;
            }
            (false, true) => {
                lhs_ty = self.check_expr(lhs, None)?;
                rhs_ty = self.check_expr(rhs, Some(lhs_ty))?;
            }
            _ => {
                lhs_ty = self.check_expr(lhs, None)?;
                rhs_ty = self.check_expr(rhs, None)?;
            }
        }

        if lhs_ty != rhs_ty {
            return Err(format!(
                "Mismatched types in binop: `{}` != `{}`",
                lhs_ty, rhs_ty
            ));
        }

        let new_ty = match sym {
            Symbol::And | Symbol::Eq | Symbol::Gt | Symbol::Lt | Symbol::Not | Symbol::Or => {
                Type::UInt32 // XXX
            }
            _ => lhs_ty,
        };

        *ty = Some(new_ty);

        Ok(new_ty)
    }

    fn check_unop(&mut self, rhs: &mut Expression, ty: &mut Option<Type>) -> Result<Type, String> {
        let rhs_ty = self.check_expr(rhs, None)?;
        *ty = Some(rhs_ty);
        Ok(rhs_ty)
    }

    fn check_cond(
        &mut self,
        cond_expr: &mut Expression,
        then_block: &mut [Node],
        else_block: &mut Option<Vec<&mut Expression>>,
        ty: &mut Option<Type>,
    ) -> Result<Type, String> {
        self.check_expr(cond_expr, None)?;

        let mut then_ty = Type::Void;
        for node in then_block {
            then_ty = self.check_node(node)?;
        }

        if let Some(else_block) = else_block {
            let mut else_ty = Type::Void;
            for expr in else_block {
                else_ty = self.check_expr(*expr, None)?;
            }

            if then_ty != else_ty {
                return Err(format!(
                    "Both arms of conditional must be the same type: `then` == {}; `else` == {}",
                    then_ty, else_ty
                ));
            }
        }

        *ty = Some(then_ty);
        Ok(then_ty)
    }
}

#[cfg(test)]
mod test {
    use insta::{with_settings, glob};

    use super::{Literal::*, TypeChecker};
    use crate::{
        ast::{Expression, Literal},
        token::{Symbol, Type}, lexer::Lexer, parser::Parser,
    };

    const ERR_STR: &str = "Numeric literal out of range";

    #[test]
    fn test_tyc_int_no_hint() {
        let literals = [
            (UInt64(7), Ok(Type::Int32)),
            (UInt64(i32::MAX as u64), Ok(Type::Int32)),
            (UInt64(i32::MAX as u64 + 1), Err(ERR_STR)),
            (Float(7.0), Ok(Type::Float)),
        ];
        let tc = TypeChecker::new();
        for mut lit in literals {
            let res = tc.check_lit(&mut lit.0, &mut None, None);
            assert_eq!(res, lit.1.map_err(|x| x.to_string()));
        }
    }

    #[test]
    fn test_tyc_int_with_hint() {
        let literals = [
            (UInt64(7), Type::Int8, Ok(Type::Int8)),
            (UInt64(i8::MAX as u64), Type::Int8, Ok(Type::Int8)),
            (UInt64(i8::MAX as u64 + 1), Type::Int8, Err(ERR_STR)),
            (UInt64(7), Type::Int16, Ok(Type::Int16)),
            (UInt64(i16::MAX as u64), Type::Int16, Ok(Type::Int16)),
            (UInt64(i16::MAX as u64 + 1), Type::Int16, Err(ERR_STR)),
            (UInt64(7), Type::Int32, Ok(Type::Int32)),
            (UInt64(i32::MAX as u64), Type::Int32, Ok(Type::Int32)),
            (UInt64(i32::MAX as u64 + 1), Type::Int32, Err(ERR_STR)),
            (UInt64(7), Type::Int64, Ok(Type::Int64)),
            (UInt64(i64::MAX as u64), Type::Int64, Ok(Type::Int64)),
            (UInt64(i64::MAX as u64 + 1), Type::Int64, Err(ERR_STR)),
            (UInt64(7), Type::UInt8, Ok(Type::UInt8)),
            (UInt64(u8::MAX as u64), Type::UInt8, Ok(Type::UInt8)),
            (UInt64(u8::MAX as u64 + 1), Type::UInt8, Err(ERR_STR)),
            (UInt64(7), Type::UInt16, Ok(Type::UInt16)),
            (UInt64(u16::MAX as u64), Type::UInt16, Ok(Type::UInt16)),
            (UInt64(u16::MAX as u64 + 1), Type::UInt16, Err(ERR_STR)),
            (UInt64(7), Type::UInt32, Ok(Type::UInt32)),
            (UInt64(u32::MAX as u64), Type::UInt32, Ok(Type::UInt32)),
            (UInt64(u32::MAX as u64 + 1), Type::UInt32, Err(ERR_STR)),
            (UInt64(7), Type::UInt64, Ok(Type::UInt64)),
            (UInt64(u64::MAX as u64), Type::UInt64, Ok(Type::UInt64)),
            (Float(7.0), Type::Float, Ok(Type::Float)),
            (Float(7.0), Type::Double, Ok(Type::Double)),
        ];

        let tc = TypeChecker::new();
        for mut lit in literals {
            let res = tc.check_lit(&mut lit.0, &mut None, Some(lit.1));
            assert_eq!(res, lit.2.map_err(|x| x.to_string()));
        }
    }

    // let x: $variant
    // x + 3
    macro_rules! test_lit_hint_binop_int {
        ($variant:ident) => {{
            let mut tc = TypeChecker::new();
            tc.check_let("x", $variant, &mut None).unwrap();
            let mut lhs = Expression::Ident {
                name: "x".to_string(),
                ty: None,
            };
            let mut rhs = Expression::Lit {
                value: Literal::UInt64(3),
                ty: None,
            };
            let res = tc.check_binop(Symbol::Add, &mut lhs, &mut rhs, &mut None);
            assert_eq!(res, Ok($variant));
        }};
    }

    // let x: $variant
    // x + 3.0
    macro_rules! test_lit_hint_binop_float {
        ($variant:ident) => {{
            let mut tc = TypeChecker::new();
            tc.check_let("x", $variant, &mut None).unwrap();
            let mut lhs = Expression::Ident {
                name: "x".to_string(),
                ty: None,
            };
            let mut rhs = Expression::Lit {
                value: Literal::Float(3.0),
                ty: None,
            };
            let res = tc.check_binop(Symbol::Add, &mut lhs, &mut rhs, &mut None);
            assert_eq!(res, Ok($variant));
        }};
    }

    #[test]
    fn test_tyc_binop_lit() {
        use Type::*;

        test_lit_hint_binop_int!(Int8);
        test_lit_hint_binop_int!(Int16);
        test_lit_hint_binop_int!(Int32);
        test_lit_hint_binop_int!(Int64);
        test_lit_hint_binop_int!(UInt8);
        test_lit_hint_binop_int!(UInt16);
        test_lit_hint_binop_int!(UInt32);
        test_lit_hint_binop_int!(UInt64);
        test_lit_hint_binop_float!(Float);
        test_lit_hint_binop_float!(Double);
    }

    #[test]
    fn test_codegen() {
        with_settings!({ snapshot_path => "tests/snapshots", prepend_module_to_snapshot => false }, {
            glob!("tests/inputs/*.input", |path| {
                let file = std::fs::File::open(path).expect("Error reading input file");
                let reader = std::io::BufReader::new(file);

                // Each line of the input files is meant to be a separate test
                // case. Treat each as its own AST. Including `ast_string` in the
                // output makes it more readable.
                let ir = reader
                    .lines()
                    .map(|line| {
                        let line = line.expect("Error reading input line");
                        let tokens = Lexer::new(&line).collect::<Result<Vec<_>, _>>().unwrap();
                        let mut ast = Parser::new(&tokens).parse().unwrap_or_else(|err| panic!("test failure in `{:?}`: {}", path, err));
                        TypeChecker::new().walk(&mut ast).unwrap_or_else(|err| panic!("test failure in `{:?}`: {}", path, err));
                        let context = Context::create();
                        let builder = context.create_builder();
                        let module = context.create_module("main_mod");
                        let fpm = PassManager::create(&module);
                        let mut codegen = Codegen::new(&context, &builder, &module, &fpm, 1, false);
                        code_to_string(codegen.walk(&ast))
                    })
                    .collect::<Vec<_>>();
                assert_yaml_snapshot!(ir);
            });
        });
    }
}
