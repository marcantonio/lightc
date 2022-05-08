use std::collections::HashMap;

use lightc::*;

use crate::ast::conversion::AsExprMut;
use crate::ast::*;
use crate::symbol_table::SymbolTable;
use crate::token::{Symbol, Type};

#[macro_use]
mod macros;

// Current performs the following tasks:
// - applies types to all expressions
// - checks for annotation consistency
// - checks for type consistency and relevance in binops
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
    // XXX: Move these to the symbol table?
    function_table: HashMap<String, FunctionEntry>,
    symbol_table: SymbolTable<Type>,
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
            symbol_table: SymbolTable::new(),
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
            Fn { proto, body } => self.check_func(proto, &mut body.as_deref_mut()),
        }
    }

    // Check function definitions. This function also does the proto.
    fn check_func(
        &mut self,
        proto: &mut Prototype,
        body: &mut Option<&mut Expression>,
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

        // Insert args into the local symbol table
        for (name, ty) in &proto.args {
            self.symbol_table.insert(name, *ty)?;
        }

        let mut body_ty = self.check_expr(body, None)?;

        // Ensure main is always an int32 and returns a 0 if nothing is
        // specified
        //
        // TODO: Should go into a desugar phase
        if proto.name == "main" {
            // If the last statement isn't an int, insert one
            match body_ty {
                int_types!() => {}
                _ => {
                    if let Expression::Block { list, .. } = body {
                        list.push(Node::Expr(Expression::Lit {
                            value: Literal::Int32(0),
                            ty: Some(Type::Int32),
                        }));
                    }
                }
            }
            body_ty = Type::Int32;
            func_entry.ret_ty = body_ty;
            proto.ret_ty = Some(body_ty);
            self.function_table
                .insert(proto.name.to_owned(), func_entry.clone());
        } else {
            // Make sure these are in sync since there's no `check_proto()`
            proto.ret_ty = Some(func_entry.ret_ty);
        }

        // Make sure function return type and the last statement match. Ignore
        // body type when proto is void.
        if func_entry.ret_ty != body_ty && func_entry.ret_ty != Type::Void {
            return Err(format!(
                "Function `{}` should return type `{}` but last statement is `{}`",
                proto.name, func_entry.ret_ty, body_ty
            ));
        }

        // Pop args
        for (name, _) in &proto.args {
            self.symbol_table.remove(name);
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
        body: &mut Expression,
    ) -> Result<(), String> {
        let start_ty = self.check_expr(start_expr, Some(start_antn))?;
        if start_antn != start_ty {
            return Err(format!(
                "Initial type mismatch in for statement. Annotated with `{}` but value is `{}`",
                start_antn, start_ty
            ));
        }

        // Remove old variable. Ignore failure. Insert starting variable.
        let old_var = self.symbol_table.remove(start_name);
        self.symbol_table.insert(start_name, start_antn)?;

        // Ensure the loop cond is always a bool
        let cond_ty = self.check_expr(cond_expr, None)?;
        if cond_ty != Type::Bool {
            return Err("For loop conditional should always be a bool".to_string());
        }

        // Make sure the step type matches the starting variable
        let step_ty = self.check_expr(step_expr, Some(start_ty))?;
        if step_ty != start_ty {
            return Err(format!(
                "Step type mismatch in for statement. Step is `{}` but `{}` is `{}`",
                step_ty, start_name, start_ty
            ));
        }

        // Check body
        self.check_expr(body, None)?;

        // Reset shadowed variable if present
        self.symbol_table.remove(start_name);
        if let Some(v) = old_var {
            self.symbol_table.insert(start_name, v)?;
        }

        Ok(())
    }

    fn check_let(
        &mut self,
        name: &str,
        antn: Type,
        init: &mut Option<&mut Expression>,
    ) -> Result<(), String> {
        // If init exists, make sure it matches the variable's annotation
        if let Some(init) = init {
            let init_ty = self.check_expr(init, Some(antn))?;
            if antn != init_ty {
                return Err(format!(
                    "Types don't match in let statement. Annotated with `{}` but initial value is `{}`",
                    antn, init_ty
                ));
            }
        }

        self.symbol_table.insert(name, antn)?;
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
            UnOp { sym, rhs, ty } => self.check_unop(*sym, rhs.as_expr_mut()?, ty),
            Call { name, args, ty } => self.check_call(name, &mut args.as_expr_mut()?, ty),
            Cond {
                cond_expr,
                then_block,
                else_block,
                ty,
            } => self.check_cond(cond_expr, then_block, &mut else_block.as_deref_mut(), ty),
            Block { list, ty } => self.check_block(list, ty),
        }
    }

    // Check the block expressions. Ensures statements always eval to void.
    fn check_block(&mut self, list: &mut [Node], ty: &mut Option<Type>) -> Result<Type, String> {
        // Drop scope
        self.symbol_table.down_scope();

        // The block type is set to the final node's type
        let mut list_ty = Type::Void;
        for node in list {
            list_ty = self.check_node(node)?;
        }
        *ty = Some(list_ty);

        // Pop up 1 level. Drops old scope.
        self.symbol_table.up_scope()?;

        Ok(list_ty)
    }

    // If there's a type hint, use it or fail. If not, use the literal's
    // type. Update `lit` with the result and return the type.
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
                    float_types!() => {
                        return Err("Literal is an integer in a float context".to_string())
                    }
                    Type::Bool => return Err("Literal is an integer in a bool context".to_string()),
                    Type::Char => return Err("Literal is an integer in a char context".to_string()),
                    _ => return Err("NONCANBE: Internal integer conversion error".to_string()),
                },
                Float(v) => match hint {
                    Type::Float => convert_num!(lit, v, Float, f32),
                    Type::Double => convert_num!(lit, v, Double, f64),
                    int_types!() => {
                        return Err("Literal is a float in an integer context".to_string())
                    }
                    Type::Bool => return Err("Literal is a float in a bool context".to_string()),
                    Type::Char => return Err("Literal is a float in a char context".to_string()),
                    _ => unreachable!("NONCANBE: Internal float conversion error"),
                },
                Double(_) => Type::Double,
                Bool(_) => Type::Bool,
                Char(_) => Type::Char,
            },
            None => match lit {
                UInt64(v) => {
                    let v = i32::try_from(*v).map_err(|_| "Numeric literal out of range")?;
                    *lit = Int32(v);
                    Type::Int32
                }
                Float(_) => Type::Float,
                Bool(_) => Type::Bool,
                Char(_) => Type::Char,
                x => unreachable!("NONCANBE: Internal numeric conversion error for {}", x),
            },
        };

        *ty = Some(lit_ty);
        Ok(lit_ty)
    }

    fn check_ident(&self, name: &str, ty: &mut Option<Type>) -> Result<Type, String> {
        let ident_ty = self
            .symbol_table
            .get(name)
            .ok_or(format!("Unknown variable: `{}`", name))?;
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

        // Check arg length
        let fe_args_len = fe_arg_tys.len();
        let args_len = args.len();
        if fe_arg_tys.len() != args.len() {
            return Err(format!(
                "Call to {} takes {} args and {} were given",
                name, fe_args_len, args_len
            ));
        }

        // Update expression type
        let ret_ty = func_entry.ret_ty;
        *ty = Some(ret_ty);

        // Check all args and record their types. Use the function entry arg
        // types as type hints.
        let mut arg_tys = Vec::with_capacity(args_len);
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
        use Symbol::*;

        // Make sure LHS is a var in assignments
        if sym == Assign && !matches!(lhs, Expression::Ident { .. }) {
            return Err("Expected LHS to be a variable for assignment".to_string());
        }

        // Check if either side is a numeric literal. If so use the other side
        // as a type hint for the literal type.
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

        // Both sides must match
        if lhs_ty != rhs_ty {
            return Err(format!(
                "Mismatched types in binop: `{}` != `{}`",
                lhs_ty, rhs_ty
            ));
        }

        // Check the operand types based on the operator used and set the
        // expression type accordingly
        let new_ty = match sym {
            And | Or => {
                if lhs_ty != Type::Bool || rhs_ty != Type::Bool {
                    return Err(format!(
                        "Expected bools on either side of `{}`, got lhs: `{}`, rhs: `{}`",
                        sym, lhs_ty, rhs_ty
                    ));
                }
                Type::Bool
            }
            Eq => {
                match (lhs_ty, rhs_ty) {
                    (
                        numeric_types!() | Type::Bool | Type::Char,
                        numeric_types!() | Type::Bool | Type::Char,
                    ) => (),
                    _ => {
                        return Err(format!(
                        "Expected numeric type on either side of `{}`, got lhs: `{}`, rhs: `{}`",
                        sym, lhs_ty, rhs_ty
                    ))
                    }
                };
                Type::Bool
            }
            Gt | Lt => {
                match (lhs_ty, rhs_ty) {
                    (numeric_types!() | Type::Char, numeric_types!() | Type::Char) => (),
                    _ => {
                        return Err(format!(
                        "Expected numeric type on either side of `{}`, got lhs: `{}`, rhs: `{}`",
                        sym, lhs_ty, rhs_ty
                    ))
                    }
                };
                Type::Bool
            }
            Add | Div | Mul | Pow | Sub => {
                match (lhs_ty, rhs_ty) {
                    (numeric_types!(), numeric_types!()) => (),
                    _ => {
                        return Err(format!(
                        "Expected numeric type on either side of `{}`, got lhs: `{}`, rhs: `{}`",
                        sym, lhs_ty, rhs_ty
                    ))
                    }
                };
                lhs_ty
            }
            _ => Type::Void,
        };

        *ty = Some(new_ty);
        Ok(new_ty)
    }

    fn check_unop(
        &mut self,
        sym: Symbol,
        rhs: &mut Expression,
        ty: &mut Option<Type>,
    ) -> Result<Type, String> {
        let rhs_ty = self.check_expr(rhs, None)?;
        match rhs_ty {
            numeric_types!() => (),
            _ => {
                return Err(format!(
                    "Expected numeric type in unary operation `{}`, got rhs: `{}`",
                    sym, rhs_ty
                ))
            }
        }
        *ty = Some(rhs_ty);
        Ok(rhs_ty)
    }

    fn check_cond(
        &mut self,
        cond_expr: &mut Expression,
        then_block: &mut Expression,
        else_block: &mut Option<&mut Expression>,
        ty: &mut Option<Type>,
    ) -> Result<Type, String> {
        let cond_ty = self.check_expr(cond_expr, None)?;
        if cond_ty != Type::Bool {
            return Err("Conditional should always be a bool".to_string());
        }

        let then_ty = self.check_expr(then_block, None)?;

        // Consequent and alternate must match if else exists
        if let Some(else_block) = else_block {
            let else_ty = self.check_expr(else_block, Some(then_ty))?;

            if then_ty != else_ty {
                return Err(format!(
                    "Both arms of conditional must be the same type: `then` == `{}`; `else` == `{}`",
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
    use std::io::BufRead;

    use super::*;
    use crate::{lexer::Lexer, parser::Parser};
    use Literal::*;

    const ERR_STR: &str = "Numeric literal out of range";

    #[test]
    fn test_type_checker() {
        insta::with_settings!({ snapshot_path => "tests/snapshots", prepend_module_to_snapshot => false }, {
            insta::glob!("tests/inputs/*.lt", |path| {
                let file = std::fs::File::open(path).expect("Error reading input file");
                let reader = std::io::BufReader::new(file);

                // Test are delimited by `#test_delim#`
                let mut asts = vec![];
                let mut test = String::new();
                for line in reader.lines() {
                    let line = line.unwrap_or_else(|_| panic!("Error reading input line in `{:?}`", path));
                    if line != "#test_delim#" {
                        test += &(line + "\n");
                    } else {
                        let tokens = Lexer::new(&test).scan().unwrap_or_else(|err| panic!("test failure in `{:?}`: {}", path, err));
                        let mut ast = Parser::new(&tokens).parse().unwrap_or_else(|err| panic!("test failure in `{:?}`: {}", path, err));
                        let res = match TypeChecker::new().walk(&mut ast) {
                            Ok(_) => Ok(ast),
                            Err(e) => Err(e),
                        };
                        asts.push((test.clone(), res));
                        test.clear();
                    }
                }
                insta::assert_yaml_snapshot!(asts);
            });
        });
    }

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
}
