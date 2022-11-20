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

type ParseResult = Result<ast::Node, ParseError>;

pub struct Parse<'a> {
    tokens: Peekable<Iter<'a, Token>>,
    symbol_table: &'a mut SymbolTable<Symbol>,
}

impl<'a> Parse<'a> {
    pub fn new(tokens: &'a [Token], symbol_table: &'a mut SymbolTable<Symbol>) -> Self {
        Parse { tokens: tokens.iter().peekable(), symbol_table }
    }

    // Parse each token using recursive descent
    //
    // StmtList ::= ( Stmt ';' )+ ;
    pub fn parse(mut self) -> Result<Ast<ast::Node>, ParseError> {
        let mut ast = Ast::new();
        while self.tokens.peek().is_some() {
            let node = self.parse_stmt()?;
            ast.add(node);
        }
        Ok(ast)
    }

    /// Statement productions

    // Stmt ::= LetStmt | ForStmt | FnDecl | ExternDecl | StructDecl | Expr ;
    fn parse_stmt(&mut self) -> ParseResult {
        let token = self.tokens.peek().ok_or_else(|| "Premature end of statement".to_string())?;

        let stmt = match &token.tt {
            TokenType::For => self.parse_for()?,
            TokenType::Let => self.parse_let()?,
            TokenType::Fn => self.parse_func()?,
            TokenType::Extern => self.parse_extern()?,
            TokenType::Struct => self.parse_struct()?,
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

        expect_next_token!(self.tokens, TokenType::OpenBrace, "Expecting `{` to start struct block");

        let mut fields = vec![];
        let mut methods = vec![];
        while let Some(t) = self.tokens.peek() {
            match &t.tt {
                TokenType::CloseBrace => {
                    self.tokens.next(); // Eat brace

                    let mut sym_fields = vec![];
                    for node in &fields {
                        // Extract fields for symbol table
                        if let ast::Node { kind: ast::node::Kind::Let { name, antn, .. } } = node {
                            sym_fields.push((name.to_owned(), antn.to_string()));
                        }
                    }

                    if self.symbol_table.insert(Symbol::new_struct(name, Some(&sym_fields))).is_some() {
                        return Err(ParseError::from((
                            format!("struct `{}` already defined", name),
                            token,
                        )));
                    }

                    return Ok(ast::Node::new_struct(name.to_owned(), fields, methods));
                },
                TokenType::Let => {
                    fields.push(self.parse_let()?);
                    self.tokens.next(); // Eat semicolon
                },
                TokenType::Fn => {
                    methods.push(self.parse_func()?);
                    self.tokens.next(); // Eat semicolon
                },
                tt => {
                    return Err(ParseError::from((
                        format!("Expecting `let` or `fn` in struct definition. Got `{}`", tt),
                        *t,
                    )))
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

    // LetStmt ::= 'let' VarInit ;
    fn parse_let(&mut self) -> ParseResult {
        self.tokens.next(); // Eat let

        let (name, antn, init) = self.parse_var_init("let")?;

        Ok(ast::Node::new_let(name, antn, init))
    }

    // FnDecl ::= Prototype Block ;
    fn parse_func(&mut self) -> ParseResult {
        // Eat 'fn'
        let token = self.tokens.next().unwrap();

        let proto = self.parse_proto()?;

        // Create symbol table entry. Use the old name as the key until later lowering.
        if self.symbol_table.insert_with_name(proto.name(), Symbol::from(&proto)).is_some() {
            return Err(ParseError::from((format!("Function `{}` can't be redefined", proto.name()), token)));
        }

        // No body for externs
        let body = if proto.is_extern() { None } else { Some(self.parse_block()?) };

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

        self.parse_func()
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
                _ => return Ok(last_expr)
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
            }
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
                _ => block.push(self.parse_stmt()?),
            }
        }

        Err(ParseError::from("Expecting `}` to terminate block".to_string()))
    }

    // IndexExpr ::= PrimaryExpr '[' Expr ']' ;
    fn parse_index(&mut self, binding: ast::Node) -> ParseResult {
        self.tokens.next(); // Eat open bracket

        let idx = self.parse_expr(0)?;

        expect_next_token!(
            self.tokens,
            TokenType::CloseBracket,
            "Expecting `]` after expression in array index"
        );

        Ok(ast::Node::new_index(binding, idx, None))
    }

    /// Literals

    // bool ::= 'true' | 'false' ;
    fn parse_lit_bool(&mut self, b: bool) -> ParseResult {
        self.tokens.next(); // Eat bool

        Ok(ast::Node::new_lit(Literal::Bool(b), None))
    }

    // CharLit ::= char ;
    // char    ::= "'" ( [^'\\r\n\t] | '\' [rnt0] ) "'" ;
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
        let (fn_name, _) =
            expect_next_token!(self.tokens, TokenType::Ident(_), "Expecting function name in prototype");

        expect_next_token!(self.tokens, TokenType::OpenParen, "Expecting `(` in prototype");

        // Parse args list
        let mut args = vec![];
        while let Some(&next) = self.tokens.peek() {
            // Matches immediate ')'
            if next.tt == TokenType::CloseParen {
                break;
            }

            // Get the name of the argument and its type annotation
            let (name, antn) = self.parse_typed_decl("prototype")?;

            args.push((name.to_string(), antn));

            // This rusty mess checks for a ',' or a ')' in the argument list. If one
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

        Ok(Prototype::new(fn_name.to_string(), args, ret_type.unwrap_or_default(), is_extern))
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
                            "Expecting a literal int for size in array type".to_string(),
                            token.unwrap(),
                        )))
                    },
                };
                expect_next_token!(
                    self.tokens,
                    TokenType::CloseBracket,
                    format!("Missing `]` in `{}` type annotation", caller)
                );
                Type::Array(Box::new(ty.as_str().into()), size.try_into().unwrap())
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
}
