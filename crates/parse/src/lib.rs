use std::iter::Peekable;
use std::num::IntErrorKind;
use std::slice::Iter;

use crate::ast::node;
use ast::Ast;
use common::{literal::Literal, Operator, Prototype, Symbol, SymbolTable, Type};
use errors::ParseError;
use lex::{Token, TokenType};
use precedence::OpPrec;

pub mod ast;
#[macro_use]
mod macros;
mod errors;
mod precedence;
#[cfg(test)]
mod tests;

#[macro_use]
extern crate common;

type ParseResult = Result<ast::Node, ParseError>;

pub struct Parse<'a> {
    tokens: Peekable<Iter<'a, Token>>,
    symbol_table: &'a mut SymbolTable<Symbol>,
    module: String,
    current_struct: Option<String>,
    imports: Vec<String>,
    errors: Vec<ParseError>,
}

impl<'a> Parse<'a> {
    pub fn new(tokens: &'a [Token], symbol_table: &'a mut SymbolTable<Symbol>) -> Self {
        Parse {
            tokens: tokens.iter().peekable(),
            symbol_table,
            module: String::new(),
            current_struct: None,
            imports: vec![],
            errors: vec![],
        }
    }

    // Parse each token using recursive descent. Returns the AST, module name, and needed
    // imports
    //
    // StmtList ::= ModDecl? ( Stmt ';' )+ ;
    pub fn parse(mut self) -> Result<(Ast<ast::Node>, String, Vec<String>), Vec<ParseError>> {
        // Ensure the file starts with a module name. No node is produced
        match self.tokens.peek() {
            Some(Token { tt: TokenType::Module, .. }) => {
                self.parse_module().unwrap_or_else(|err| self.push_err(err))
            },
            // If no module is declared, assume it's `main` for now
            _ => {
                self.module = String::from("main");
            },
        };

        let mut ast = Ast::new();
        while self.tokens.peek().is_some() {
            match self.parse_stmt() {
                Ok(n) if self.errors.is_empty() & !n.is_blank() => ast.add(n),
                Err(e) => self.push_err(e),
                _ => continue,
            };
        }
        if self.errors.is_empty() {
            Ok((ast, self.module, self.imports))
        } else {
            Err(self.errors)
        }
    }

    /// Statement productions

    // Stmt ::= LetStmt | ForStmt | LoopStmt | WhileStmt | FnDecl | ExternDecl
    //          | StructDecl | UseStmt | BreakStmt | NextStmt | Expr ;

    fn parse_stmt(&mut self) -> ParseResult {
        use TokenType::*;

        let token = self.tokens.peek().ok_or_else(|| "Premature end of statement".to_string())?;

        let stmt = match &token.tt {
            For => self.parse_for()?,
            Loop => self.parse_loop()?,
            While => self.parse_while()?,
            Let => self.parse_let()?,
            Fn => self.parse_fn()?,
            Extern => self.parse_extern()?,
            Struct => self.parse_struct()?,
            Use => self.parse_use()?,
            Break => self.parse_break()?,
            Next => self.parse_next()?,
            _ => self.parse_expr(0)?,
        };

        // Semicolon is optional when next token is a '}'
        if !matches!(self.tokens.peek(), Some(&Token { tt: TokenType::CloseBrace, .. })) {
            expect_next_token!(self.tokens, TokenType::Semicolon(_), "Missing semicolon to end statement");
        }

        Ok(stmt)
    }

    // StructDecl ::= 'struct' ident '{' ( LetStmt ';' | FnDecl ';' )* '}' ;
    fn parse_struct(&mut self) -> ParseResult {
        self.tokens.next(); // Eat struct

        let (name, token) =
            expect_next_token!(self.tokens, TokenType::Ident(_), "Expecting struct name in declaration");

        let full_name = format!("{}::{}", self.module, name);

        expect_next_token!(self.tokens, TokenType::OpenBrace, "Expecting `{` to start struct block");

        let mut fields = vec![];
        let mut methods = vec![];
        while let Some(t) = self.tokens.peek() {
            match &t.tt {
                TokenType::CloseBrace => {
                    self.tokens.next(); // Eat brace

                    // Collect all fields for struct symbol table entry
                    let mut sym_fields = vec![];
                    for node in &fields {
                        if let ast::Node { kind: ast::node::Kind::Let { name, antn, .. } } = node {
                            sym_fields.push((name.to_owned(), antn.to_string()));
                        }
                    }

                    // Add method names to struct symbol
                    let mut sym_methods = vec![];
                    for node in methods.iter_mut() {
                        if let ast::Node { kind: ast::node::Kind::Fn { proto, .. } } = node {
                            // TODO: remove this when `orig_name` becomes part of Prototype
                            let simple_name = proto.name().split('_').nth(2).unwrap_or_else(|| {
                                unreachable!("couldn't split prototype name in `parse_struct()`")
                            });
                            sym_methods.push(simple_name.to_owned());
                        }
                    }

                    // Insert struct into symbol table
                    if self
                        .symbol_table
                        .insert(Symbol::new_struct(
                            &full_name,
                            Some(&sym_fields),
                            Some(&sym_methods),
                            &self.module,
                            true,
                        ))
                        .is_some()
                    {
                        return Err(ParseError::from((
                            format!("struct `{}` already defined", full_name),
                            token,
                        )));
                    }

                    return Ok(ast::Node::new_struct(full_name, fields, methods));
                },
                TokenType::Let => {
                    match self.parse_let() {
                        Ok(l) => fields.push(l),
                        Err(e) => self.push_err(e),
                    }
                    token_is_and_then!(self.tokens.peek(), TokenType::Semicolon(_), {
                        self.tokens.next(); // Eat semicolon
                    });
                },
                TokenType::Fn => {
                    self.current_struct = Some(full_name.to_owned());
                    match self.parse_fn() {
                        Ok(f) => methods.push(f),
                        Err(e) => self.push_err(e),
                    }
                    token_is_and_then!(self.tokens.peek(), TokenType::Semicolon(_), {
                        self.tokens.next(); // Eat semicolon
                    });
                    self.current_struct = None;
                },
                tt => {
                    // Do not propagate a ParseError within a struct or the struct will
                    // not be parsed, causing incorrect errors
                    let e = ParseError::from((
                        format!("Expecting `let` or `fn` in struct definition. Got `{}`", tt),
                        *t,
                    ));
                    if let Some(t) = self.tokens.peek() {
                        if t.tt == TokenType::OpenBrace {
                            // If token is an open brace, parse it as a stmt allows it to
                            // parse generic blocks within a struct
                            self.parse_stmt()?;
                        } else {
                            self.push_err(e);
                        }
                    } else {
                        self.push_err(e);
                    }
                },
            }
        }

        Err(ParseError::from("Expecting `}` to terminate struct definition".to_string()))
    }

    // ForStmt ::= 'for' VarInit ';' Expr ';' number? Block ;
    fn parse_for(&mut self) -> ParseResult {
        self.tokens.next(); // Eat for

        let (name, antn, init) = self.parse_var_init("for")?;

        expect_explicit_semi!(self.tokens, "Expecting `;` after starting expression");

        let cond_node = self.parse_expr(0)?;
        expect_explicit_semi!(self.tokens, "Expecting `;` after condition");

        let step_node = self.parse_expr(0)?;

        Ok(ast::Node::new_for(name, antn, init, cond_node, step_node, self.parse_block()?))
    }

    // LoopStmt ::= 'loop' Block ;
    fn parse_loop(&mut self) -> ParseResult {
        self.tokens.next(); // Eat loop
        Ok(ast::Node::new_loop(self.parse_block()?))
    }

    // WhileStmt ::= 'while' Expr Block ;
    fn parse_while(&mut self) -> ParseResult {
        self.tokens.next(); // Eat while
        Ok(ast::Node::new_while(self.parse_expr(0)?, self.parse_block()?))
    }

    // LetStmt ::= 'let' VarInit ;
    fn parse_let(&mut self) -> ParseResult {
        self.tokens.next(); // Eat let
        let (name, antn, init) = self.parse_var_init("let")?;

        Ok(ast::Node::new_let(name, antn, init))
    }

    // FnDecl ::= Prototype Block ;
    fn parse_fn(&mut self) -> ParseResult {
        // Eat 'fn'
        let token = self.tokens.next().unwrap();

        let mut proto = self.parse_proto()?;

        // No body for externs
        let body = if proto.is_extern() { None } else { Some(self.parse_block()?) };

        // Create symbol table entry. Use the old name as the key until later lowering.
        //
        // For methods use a "semi" lowered name. We do this here to allow for proper name
        // collision detection in the tych
        if let Some(struct_name) = &self.current_struct {
            let orig_name = proto.name().to_owned();
            let method_name = format!("_{}_{}", struct_name, proto.name());
            proto.set_name(method_name);

            // Insert `self` for methods. Do this early so we don't have to mess with the
            // symbol table later. `self` will be passed as a pointer
            let mut args = vec![(String::from("self"), pointer_wrap!(Type::Comp(struct_name.clone())))];
            args.append(&mut proto.params().to_vec());
            proto.set_params(args);

            if self.symbol_table.insert_with_name(proto.name(), Symbol::from(&proto)).is_some() {
                return Err(ParseError::from((
                    format!("method `{}` can't be redefined on `{}`", orig_name, struct_name),
                    token,
                )));
            }
        } else {
            let sym = self.symbol_table.insert_with_name(proto.name(), Symbol::from(&proto));
            // Error on dups. Ignore for externs
            if sym.is_some() && body.is_some() {
                return Err(ParseError::from((
                    format!("function `{}` can't be redefined", proto.name()),
                    token,
                )));
            }
        }

        Ok(ast::Node::new_fn(proto, body))
    }

    // ExternDecl ::= 'extern' Prototype ;
    fn parse_extern(&mut self) -> ParseResult {
        // Eat 'extern'
        self.tokens.next();

        let next = self.tokens.peek();
        if !matches!(next, Some(Token { tt: TokenType::Fn, .. })) {
            return Err(ParseError::from((String::from("Expecting `fn` after `extern`"), *next.unwrap())));
        }

        self.parse_fn()
    }

    // ModDecl ::= 'module' ident ';' ;
    fn parse_module(&mut self) -> Result<(), ParseError> {
        self.tokens.next(); // Eat module

        let (name, _) =
            expect_next_token!(self.tokens, TokenType::Ident(_), "Expecting module name after `module`");

        self.module = name.to_owned();

        self.tokens.next(); // Eat semicolon
        Ok(())
    }

    // UseStmt ::= 'use' ident
    fn parse_use(&mut self) -> ParseResult {
        self.tokens.next(); // Eat use

        let (name, _) =
            expect_next_token!(self.tokens, TokenType::Ident(_), "Expecting module name after `use`");
        self.imports.push(name.to_owned());

        Ok(ast::Node::new_blank())
    }

    // BreakStmt ::= 'break' ;
    fn parse_break(&mut self) -> ParseResult {
        self.tokens.next(); // Eat break
        Ok(ast::Node::new_break())
    }

    // NextStmt ::= 'next' ;
    fn parse_next(&mut self) -> ParseResult {
        self.tokens.next(); // Eat next
        Ok(ast::Node::new_next())
    }

    /// Expression productions

    // Parses arbitrary length binary expressions. Uses Pratt with operator
    // precedence parsing.
    //
    // Expr ::= PrimaryExpr | Expr mul_op Expr | Expr add_op Expr | Expr rel_op Expr
    //        | Expr eq_op Expr | Expr bit_op Expr | Expr '&&' Expr | Expr '||' Expr
    //        | AssignableExpr assign_op Expr ;
    fn parse_expr(&mut self, min_p: u8) -> ParseResult {
        let mut lhs = self.parse_primary()?;

        // Peek at the next token, otherwise return current lhs
        while let Some(next) = self.tokens.peek() {
            // Should always be an operator after a primary
            let op = match next.tt {
                TokenType::Op(s) => s,
                _ => break,
            };

            // Determine operator precedence and associativity.
            // Stop eating and return the lhs if the current op:
            //   - is lower precedence than the last one (min_p), or:
            //   - is the same precedence and associates left
            let p = match OpPrec::bin_prec(op)? {
                OpPrec::Left(p) => {
                    if p <= min_p {
                        break;
                    }
                    p
                },
                OpPrec::Right(p) => {
                    if p < min_p {
                        break;
                    }
                    p
                },
            };

            // Advance past op
            self.tokens.next();

            // Descend for rhs with the current precedence as min_p
            let rhs = self.parse_expr(p)?;

            // Make a new lhs and continue loop
            lhs = ast::Node::new_binop(op, lhs, rhs, None);
        }
        Ok(lhs)
    }

    // UnopExpr ::= ( '-' | '!' ) Expr ;
    fn parse_unop(&mut self, op: Operator) -> ParseResult {
        self.tokens.next(); // Eat operator

        let p = OpPrec::un_prec(op)?;
        let rhs = self.parse_expr(p)?;
        Ok(ast::Node::new_unop(op, rhs, None))
    }

    // PrimaryExpr ::= CondExpr | LitExpr | IdentExpr | CallExpr | Block
    //               | ParenExpr | IndexExpr | SelfExpr | FieldSelectorExpr
    //               | MethodExpr ;
    fn parse_primary(&mut self) -> ParseResult {
        use TokenType::*;

        let token = self.tokens.peek().cloned().ok_or_else(|| "Premature end of expression".to_string())?;

        let expr = match &token.tt {
            If => self.parse_cond()?,
            Ident(id) => self.parse_ident(id)?,
            OpenBrace => self.parse_block()?,
            OpenParen => self.parse_paren()?,
            Op(sym) => self.parse_unop(*sym)?,
            Bool(b) => self.parse_lit_bool(*b)?,
            Char(c) => self.parse_lit_char(c, token)?,
            Num(num) => self.parse_lit_num(num, token)?,
            Str(s) => self.parse_lit_string(s)?,
            OpenBracket => self.parse_lit_array()?,
            x => return Err(ParseError::from((format!("Expecting primary expression. Got `{}`", x), token))),
        };

        // To support chaining selectors and indexing, repeatedly check the next token:
        //   - if it's a '[', this primary is the target array
        //   - if it's a '.', this primary is the target struct
        //
        // NB: This works with `peek()` because `parse_*` will advance the tokens.
        let mut last_expr = expr;
        while let Some(token) = self.tokens.peek() {
            last_expr = match token {
                Token { tt: OpenBracket, .. } => self.parse_index(last_expr)?,
                Token { tt: Dot, .. } => self.parse_selector(last_expr)?,
                _ => return Ok(last_expr),
            };
        }
        Ok(last_expr)
    }

    // Entry point for variables and function calls
    //
    // IdentExpr ::= ident ;
    // CallExpr  ::= ident '(' ExprList? ')' ;
    fn parse_ident(&mut self, id: &str) -> ParseResult {
        self.tokens.next(); // Eat ident

        match self.tokens.peek() {
            Some(Token { tt: TokenType::OpenParen, .. }) => {
                // Eat open paren
                self.tokens.next();
                // Parse argument list
                let args = self.parse_expr_list(TokenType::CloseParen, "function call argument list")?;
                // Eat close paren
                expect_next_token!(self.tokens, TokenType::CloseParen, "Expecting `)` in function call");
                Ok(ast::Node::new_call(id.to_owned(), args, None))
            },
            _ => Ok(ast::Node::new_ident(id.to_owned(), None)),
        }
    }

    // Entry point for field and method selectors
    //
    // FieldSelectorExpr  ::= PrimaryExpr '.' IdentExpr ;
    // MethodSelectorExpr ::= PrimaryExpr '.' CallExpr ;
    fn parse_selector(&mut self, target: ast::Node) -> ParseResult {
        self.tokens.next(); // Eat dot

        let (ident, _) = expect_next_token!(
            self.tokens,
            TokenType::Ident(_),
            "Expecting field or method name after struct selector"
        );

        match self.tokens.peek() {
            Some(Token { tt: TokenType::OpenParen, .. }) => {
                // Eat open paren
                self.tokens.next();
                // Parse argument list
                let args = self.parse_expr_list(TokenType::CloseParen, "method call argument list")?;
                // Eat close paren
                expect_next_token!(self.tokens, TokenType::CloseParen, "Expecting `)` in method call");
                Ok(ast::Node::new_mselector(target, ident.to_owned(), args, None))
            },
            _ => Ok(ast::Node::new_fselector(target, ident.to_owned(), None)),
        }
    }

    // ParenExpr ::= '(' Expr ')' ;
    fn parse_paren(&mut self) -> ParseResult {
        self.tokens.next(); // Eat '('
        let lhs = self.parse_expr(0);
        expect_next_token!(self.tokens, TokenType::CloseParen, "Expecting `)` to close paren expression");
        lhs
    }

    // CondExpr ::= 'if' Expr Block ( 'else' (CondExpr | Block ) )? ;
    fn parse_cond(&mut self) -> ParseResult {
        self.tokens.next(); // Eat if

        let cond_expr = self.parse_expr(0)?;
        let then_block = self.parse_block()?;

        let else_block = token_is_and_then!(self.tokens.peek(), TokenType::Else, {
            self.tokens.next(); // Eat else

            // To support `else if`, peek to check for `{` or `if`
            let next = self.tokens.peek();
            if matches!(next, Some(t) if t.tt != TokenType::If && t.tt != TokenType::OpenBrace) {
                return Err(ParseError::from((
                    "Expecting `if` or `{` after `else`".to_string(),
                    *next.unwrap(),
                )));
            }

            // If there's another `if`, put it the `else_block` vec
            if let Some(TokenType::If) = self.tokens.peek().map(|t| &t.tt) {
                // An `if` is always an expression so this is ok
                ast::Node::new_block(vec![self.parse_expr(0)?], None)
            } else {
                self.parse_block()?
            }
        });

        Ok(ast::Node::new_cond(cond_expr, then_block, else_block, None))
    }

    // Block ::= '{' StmtList? '}' ;
    fn parse_block(&mut self) -> ParseResult {
        let mut block: Vec<ast::Node> = vec![];

        expect_next_token!(self.tokens, TokenType::OpenBrace, "Expecting `{` to start block");

        while let Some(t) = self.tokens.peek() {
            match t.tt {
                TokenType::CloseBrace => {
                    self.tokens.next();
                    return Ok(ast::Node::new_block(block, None));
                },
                _ => {
                    // Do not propagate a ParseError within a block or the block will not
                    // be parsed, causing incorrect errors
                    match self.parse_stmt() {
                        Ok(b) => block.push(b),
                        Err(e) => self.push_err(e),
                    }
                },
            }
        }

        Err(ParseError::from("Expecting `}` to terminate block".to_string()))
    }

    // IndexExpr ::= PrimaryExpr '[' Expr ']' ;
    fn parse_index(&mut self, binding: ast::Node) -> ParseResult {
        self.tokens.next(); // Eat open bracket

        let idx = self.parse_expr(0)?;

        expect_next_token!(self.tokens, TokenType::CloseBracket, "Expecting `]` after expression in index");

        Ok(ast::Node::new_index(binding, idx, None))
    }

    /// Literals
    // LitExpr ::= number | bool | CharLit | StringLit | ArrayLit ;

    // bool ::= 'true' | 'false' ;
    fn parse_lit_bool(&mut self, b: bool) -> ParseResult {
        self.tokens.next(); // Eat bool

        Ok(ast::Node::new_lit(Literal::Bool(b), None))
    }

    // CharLit ::= char ;
    // esc_seq ::= '\' [rnt0'"\] ;
    // char    ::= "'" ( esc_seq | [^\r\n\\'] ) "'" ;
    fn parse_lit_char(&mut self, c: &str, token: &Token) -> ParseResult {
        self.tokens.next(); // Eat char

        match c.parse::<char>() {
            Ok(c) => Ok(ast::Node::new_lit(Literal::Char(c as u8), None)),
            Err(_) => Err(ParseError::from((format!("Invalid character literal: {}", token), token))),
        }
    }

    // Literal numbers are u64 or f64
    // TODO: Revisit when we have literal annotations, i.e., 78int64.
    //
    // number  ::= integer | float ;
    // integer ::= digit+ ;
    // float   ::= digit '.' digit ;
    // digit   ::= [0-9] ;
    fn parse_lit_num(&mut self, n: &str, token: &Token) -> ParseResult {
        self.tokens.next(); // Eat num

        match n.parse::<u64>() {
            Ok(n) => Ok(ast::Node::new_lit(Literal::UInt64(n), None)),
            Err(e) if e.kind() == &IntErrorKind::PosOverflow || e.kind() == &IntErrorKind::NegOverflow => {
                Err(ParseError::from((format!("Numeric literal out of integer range: {}", token), token)))
            },
            _ => match n.parse::<f32>() {
                Ok(n) => Ok(ast::Node::new_lit(Literal::Float(n), None)),
                Err(_) => Err(ParseError::from((format!("Invalid numeric literal: {}", token), token))),
            },
        }
    }

    // StringLit ::= string ;
    // string    ::= '"' ( esc_seq | [^\r\n\\""])* '"' ;
    fn parse_lit_string(&mut self, s: &str) -> ParseResult {
        self.tokens.next(); // Eat string

        Ok(ast::Node::new_lit(Literal::Str(s.to_string()), None))
    }

    // ArrayLit ::= '[' ExprList? ']' ;
    fn parse_lit_array(&mut self) -> ParseResult {
        self.tokens.next(); // Eat open bracket

        let elements = self.parse_expr_list(TokenType::CloseBracket, "array literal")?;

        // Eat close bracket
        expect_next_token!(self.tokens, TokenType::CloseBracket, "Expecting `]` in array literal");

        Ok(ast::Node::new_lit(Literal::Array { elements, inner_ty: None }, None))
    }

    /// Misc productions

    // Prototype ::= 'fn' ident '(' ( TypedDecl ( ',' TypedDecl )* )* ')' ( '->' TypeAntn )? ;
    fn parse_proto(&mut self) -> Result<Prototype, ParseError> {
        let (name, _) =
            expect_next_token!(self.tokens, TokenType::Ident(_), "Expecting function name in prototype");

        expect_next_token!(self.tokens, TokenType::OpenParen, "Expecting `(` in prototype");

        // Parse parameter list
        let mut params = vec![];
        while let Some(&next) = self.tokens.peek() {
            // Matches immediate ')'
            if next.tt == TokenType::CloseParen {
                break;
            }

            // Get the name of the parameter and its type annotation
            let (name, antn) = self.parse_typed_decl("prototype")?;

            params.push((name.to_string(), antn));

            // This rusty mess checks for a ',' or a ')' in the parameter list. If one
            // isn't found we try to create a new "error token" with the right context for
            // the error message. If the bad token is an implicit semicolon, take the next
            // one in the list or use EOF.
            match self.tokens.peek().cloned() {
                Some(Token { tt: TokenType::CloseParen, .. }) => break,
                Some(Token { tt: TokenType::Comma, .. }) => self.tokens.next(), // Eat comma
                Some(t) => {
                    let new_t = Token::new(TokenType::Eof, t.line, t.column);
                    let err_token = if t.is_implicit_semi() {
                        self.tokens.next(); // Eat semicolon
                        let next = self.tokens.peek();
                        match next {
                            Some(n) if !n.is_eof() => (*n).clone(),
                            _ => new_t,
                        }
                    } else {
                        t.clone()
                    };
                    return Err(ParseError::from((
                        format!("Expecting `,` or `)` in prototype. Got `{}`", &err_token),
                        &err_token,
                    )));
                },
                None => unreachable!("token can't be None in prototype"),
            };
        }

        // Eat close paren
        self.tokens.next();

        // Parse return type
        let mut ret_type = None;
        if let Some(next) = self.tokens.peek() {
            ret_type = match next.tt {
                TokenType::Op(Operator::RetType) => {
                    self.tokens.next();
                    Some(self.parse_type_antn("prototype")?)
                },
                _ => None,
            };
        }

        // If the next token is a ';', this is an extern
        let is_extern = matches!(&self.tokens.peek(), Some(Token { tt: TokenType::Semicolon(..), .. }));

        Ok(Prototype::new(
            name.to_owned(),
            params,
            ret_type.unwrap_or_default(),
            is_extern,
            self.module.clone(),
            self.current_struct.clone(),
        ))
    }

    // VarInit ::= TypedDecl ( '=' Expr  )? ;
    fn parse_var_init(&mut self, caller: &str) -> Result<(String, Type, Option<ast::Node>), ParseError> {
        // Get the name of the variable and its type annotation
        let (name, antn) = self.parse_typed_decl(caller)?;

        // Get the optional initial value
        let init = token_is_and_then!(self.tokens.peek(), TokenType::Op(Operator::Assign), {
            self.tokens.next();
            self.parse_expr(0)?
        });

        Ok((name, antn, init))
    }

    // TypeAntn ::= type | '[' type ']' ;
    fn parse_type_antn(&mut self, caller: &str) -> Result<Type, ParseError> {
        let token = self.tokens.next();
        let ty = match token {
            Some(Token { tt: TokenType::OpenBracket, .. }) => {
                let (ty, _) = expect_next_token!(
                    self.tokens,
                    TokenType::Ident(_),
                    format!("Expecting identifier after `[` in `{}` type annotation", caller)
                );
                expect_next_token!(
                    self.tokens,
                    TokenType::Semicolon(_),
                    format!("Expecting semicolon after `{}` in `{}` type annotation", ty, caller)
                );

                let size = match self.parse_expr(0)? {
                    ast::Node { kind: node::Kind::Lit { value: Literal::UInt64(s), .. } } => s,
                    _ => {
                        return Err(ParseError::from((
                            "Expecting a literal int for size in sarray type".to_string(),
                            token.unwrap(),
                        )))
                    },
                };
                expect_next_token!(
                    self.tokens,
                    TokenType::CloseBracket,
                    format!("Missing `]` in `{}` type annotation", caller)
                );
                Type::SArray(Box::new(ty.as_str().into()), size.try_into().unwrap())
            },
            Some(Token { tt: TokenType::Ident(ty), .. }) => ty.as_str().into(),
            Some(next) => {
                return Err(ParseError::from((
                    format!("Expecting {} type annotation. Got `{}`", caller, next),
                    next,
                )))
            },
            None => {
                return Err(ParseError::from((
                    format!("Expecting type annotation in `{}`. Got `EOF`", caller),
                    Token::default(),
                )))
            },
        };
        Ok(ty)
    }

    // TypedDecl ::= ident ':' TypeAntn ;
    fn parse_typed_decl(&mut self, caller: &str) -> Result<(String, Type), ParseError> {
        let err = match caller {
            "prototype" => format!("Expecting identifier or `)` in `{}` typed declaration", caller),
            _ => format!("Expecting identifier in `{}` typed declaration", caller),
        };

        let (name, _) = expect_next_token!(self.tokens, TokenType::Ident(_), err);

        expect_next_token!(
            self.tokens,
            TokenType::Colon,
            format!("Expecting `:` after identifier in `{}` typed declaration", caller)
        );
        Ok((name.to_owned(), self.parse_type_antn(caller)?))
    }

    // ExprList ::= Expr ','? | Expr ( ',' Expr )* ;
    fn parse_expr_list(&mut self, term: TokenType, in_err: &str) -> Result<Vec<ast::Node>, ParseError> {
        let mut args: Vec<ast::Node> = vec![];
        while let Some(&next) = self.tokens.peek() {
            // Matches immediate terminator
            if next.tt == term {
                break;
            }

            args.push(self.parse_expr(0)?);

            match self.tokens.peek() {
                Some(Token { tt, .. }) if tt == &term => break,
                Some(Token { tt: TokenType::Comma, .. }) => self.tokens.next(), // Eat comma
                _ => {
                    return Err(ParseError::from((
                        format!("Expecting `,` or `{}` in {}. Got `{}`", term, in_err, next),
                        next,
                    )))
                },
            };
        }
        Ok(args)
    }

    // Add error to parse errors and try to recover
    fn push_err(&mut self, e: ParseError) {
        self.errors.push(e);
        self.recover();
    }

    // Move iterator to recoverable position
    fn recover(&mut self) {
        while self.tokens.peek().is_some() {
            if self.at_panic_stop_token() {
                break;
            } else {
                self.tokens.next();
            }
        }
    }

    // True if iterator is at a panic_stop_token. Moves iterator to proper location
    // depending on the stop token that is detected for optimal error recovery.
    fn at_panic_stop_token(&mut self) -> bool {
        use TokenType::*;
        if let Some(t) = self.tokens.peek() {
            if matches!(t.tt, Semicolon(true)) {
                // Only implicit semis in case error is within a for-loop
                self.tokens.next();
                true
            } else {
                match t.tt {
                    // Do not move past OpenBrace so block can be parsed
                    OpenBrace => true,
                    _ => false,
                }
            }
        } else {
            false
        }
    }
}
