use std::iter::Peekable;
use std::num::IntErrorKind;
use std::slice::Iter;

use self::errors::ParseError;
use self::precedence::OpPrec;
use ast::{Ast, Expression, Literal, Node, Prototype, Statement};
use common::{Operator, SymbolTable, Token, TokenType, Type};

#[macro_use]
mod macros;
mod errors;
mod precedence;
#[cfg(test)]
mod tests;

type ParseResult = Result<Node, ParseError>;

pub struct Parser<'a> {
    ast: Ast<Node>,
    _symbol_table: &'a mut SymbolTable,
    tokens: Peekable<Iter<'a, Token>>,
}

impl<'a> Parser<'a> {
    pub fn new(tokens: &'a [Token], symbol_table: &'a mut SymbolTable) -> Self {
        Parser { ast: Ast::new(), _symbol_table: symbol_table, tokens: tokens.iter().peekable() }
    }

    // Parse each token using recursive descent
    //
    // StmtList ::= ( Stmt ';' )+ ;
    pub fn parse(mut self) -> Result<Ast<Node>, ParseError> {
        while self.tokens.peek().is_some() {
            let node = self.parse_stmt()?;
            self.ast.add(node);
        }
        Ok(self.ast)
    }

    /// Statement productions

    // Stmt ::= LetStmt | ForStmt | FnDecl | ExternDecl | StructDecl | Expr ;
    fn parse_stmt(&mut self) -> ParseResult {
        let token = self.tokens.peek().ok_or_else(|| "Premature end of statement".to_string())?;

        let stmt = match &token.tt {
            TokenType::For => self.parse_for()?,
            TokenType::Let => self.parse_let()?,
            TokenType::Fn => self.parse_function()?,
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

        let struct_name =
            expect_next_token!(self.tokens, TokenType::Ident(_), "Expecting struct name in declaration");

        expect_next_token!(self.tokens, TokenType::OpenBrace, "Expecting `{` to start struct block");

        let mut attributes = vec![];
        let mut methods = vec![];
        while let Some(t) = self.tokens.peek() {
            match &t.tt {
                TokenType::CloseBrace => {
                    self.tokens.next();
                    return Ok(Node::Stmt(Statement::Struct {
                        name: struct_name.to_owned(),
                        attributes,
                        methods,
                    }));
                },
                TokenType::Let => {
                    attributes.push(self.parse_let()?);
                    self.tokens.next(); // Eat semicolon
                },
                TokenType::Fn => {
                    methods.push(self.parse_function()?);
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

        Ok(Node::Stmt(Statement::For {
            start_name: name,
            start_antn: antn,
            start_expr: init.map(Box::new),
            cond_expr: Box::new(cond_node),
            step_expr: Box::new(step_node),
            body: Box::new(self.parse_block()?),
        }))
    }

    // LetStmt ::= 'let' VarInit ;
    fn parse_let(&mut self) -> ParseResult {
        self.tokens.next(); // Eat let

        let (name, antn, init) = self.parse_var_init("let")?;

        Ok(Node::Stmt(Statement::Let { name, antn, init: init.map(Box::new) }))
    }

    // FnDecl ::= Prototype Block ;
    fn parse_function(&mut self) -> ParseResult {
        // Eat 'fn'
        self.tokens.next();

        Ok(Node::Stmt(Statement::Fn {
            proto: Box::new(self.parse_proto()?),
            body: Some(Box::new(self.parse_block()?)),
        }))
    }

    // ExternDecl ::= 'extern' Prototype ;
    fn parse_extern(&mut self) -> ParseResult {
        // Eat 'extern'
        self.tokens.next();

        Ok(Node::Stmt(Statement::Fn { proto: Box::new(self.parse_proto()?), body: None }))
    }

    /// Expression productions

    // Parses arbitrary length binary expressions. Uses Pratt with operator
    // precedence parsing.
    //
    // Expr ::= PrimaryExpr | Expr mul_op Expr | Expr add_op Expr | Expr rel_op Expr
    //        | Expr eq_op Expr | Expr bit_op Expr | Expr '&&' Expr | Expr '||' Expr
    //        | ( IdentExpr SelfExpr ) assign_op Expr ;
    fn parse_expr(&mut self, min_p: u8) -> ParseResult {
        let mut lhs = self.parse_primary()?;

        // Peek at the next token, otherwise return current lhs
        while let Some(next) = self.tokens.peek() {
            // Should always be an operator after a primary
            let op = match next.tt {
                TokenType::Op(s) => s,
                // Start a new expression if we see two primaries in a row
                // XXX: really?
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
            lhs = Node::Expr(Expression::BinOp { op, lhs: Box::new(lhs), rhs: Box::new(rhs), ty: None });
        }
        Ok(lhs)
    }

    // UnopExpr ::= ( '-' | '!' ) Expr ;
    fn parse_unop(&mut self, op: Operator) -> ParseResult {
        self.tokens.next(); // Eat operator

        let p = OpPrec::un_prec(op)?;
        let rhs = self.parse_expr(p)?;
        Ok(Node::Expr(Expression::UnOp { op, rhs: Box::new(rhs), ty: None }))
    }

    // PrimaryExpr ::= CondExpr | | SelfExpr |LitExpr | IdentExpr | CallExpr | Assignment
    //               | Block | ParenExpr | IndexExpr ;
    // LitExpr     ::= number | bool | CharLit | ArrayLit ;
    fn parse_primary(&mut self) -> ParseResult {
        use TokenType::*;

        let token = self.tokens.peek().cloned().ok_or_else(|| "Premature end of expression".to_string())?;

        let expr = match &token.tt {
            If => self.parse_cond()?,
            Ident(id) => self.parse_ident_or_call(id)?,
            OpenBrace => self.parse_block()?,
            OpenParen => self.parse_paren()?,
            Op(sym) => self.parse_unop(*sym)?,
            Bool(b) => self.parse_lit_bool(*b)?,
            Char(c) => self.parse_lit_char(c, token)?,
            Num(num) => self.parse_lit_num(num, token)?,
            OpenBracket => self.parse_lit_array()?,
            x => return Err(ParseError::from((format!("Expecting primary expression. Got `{}`", x), token))),
        };

        // Array indices come after the primary
        if matches!(self.tokens.peek(), Some(Token { tt: OpenBracket, .. })) {
            self.parse_index(expr)
        } else {
            Ok(expr)
        }
    }

    // Variable or function call
    // TODO: break these up
    //
    // IdentExpr ::= ident ;
    // CallExpr  ::= ident '(' ExprList? ')' ;
    // ident     ::= letter ( letter | digit | '_' )* ;
    fn parse_ident_or_call(&mut self, id: &str) -> ParseResult {
        self.tokens.next(); // Eat ident

        let node = Expression::Ident { name: id.to_owned(), ty: None };

        // If next is not a '(', the current token is just a simple var
        match self.tokens.peek() {
            Some(Token { tt: TokenType::OpenParen, .. }) => (),
            _ => return Ok(Node::Expr(node)),
        };

        // Eat open paren
        self.tokens.next();

        // Parse argument list
        let args = self.parse_expr_list(TokenType::CloseParen, "function call argument list")?;

        // Eat close paren
        expect_next_token!(self.tokens, TokenType::CloseParen, "Expecting `)` in function call");

        Ok(Node::Expr(Expression::Call { name: id.to_owned(), args, ty: None }))
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

        let cond_node = self.parse_expr(0)?;
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
                Node::Expr(Expression::Block { list: vec![self.parse_expr(0)?], ty: None })
            } else {
                self.parse_block()?
            }
        });

        Ok(Node::Expr(Expression::Cond {
            cond_expr: Box::new(cond_node),
            then_block: Box::new(then_block),
            else_block: else_block.map(Box::new),
            ty: None,
        }))
    }

    // Block ::= '{' StmtList? '}' ;
    fn parse_block(&mut self) -> ParseResult {
        let mut block: Vec<Node> = vec![];

        expect_next_token!(self.tokens, TokenType::OpenBrace, "Expecting `{` to start block");

        while let Some(t) = self.tokens.peek() {
            match t.tt {
                TokenType::CloseBrace => {
                    self.tokens.next();
                    return Ok(Node::Expr(Expression::Block { list: block, ty: None }));
                },
                _ => block.push(self.parse_stmt()?),
            }
        }

        Err(ParseError::from("Expecting `}` to terminate block".to_string()))
    }

    // IndexExpr ::= PrimaryExpr '[' Expr ']' ;
    fn parse_index(&mut self, binding: Node) -> ParseResult {
        self.tokens.next(); // Eat open bracket

        let index = self.parse_expr(0)?;

        expect_next_token!(
            self.tokens,
            TokenType::CloseBracket,
            "Expecting `]` after expression in array index"
        );

        Ok(Node::Expr(Expression::Index { binding: Box::new(binding), idx: Box::new(index), ty: None }))
    }

    /// Literals

    // bool ::= 'true' | 'false' ;
    fn parse_lit_bool(&mut self, b: bool) -> ParseResult {
        self.tokens.next(); // Eat bool

        Ok(Node::Expr(Expression::Lit { value: Literal::Bool(b), ty: None }))
    }

    // CharLit ::= char ;
    // char    ::= "'" ( [^'\\r\n\t] | '\' [rnt0] ) "'" ;
    fn parse_lit_char(&mut self, c: &str, token: &Token) -> ParseResult {
        self.tokens.next(); // Eat char

        match c.parse::<char>() {
            Ok(c) => Ok(Node::Expr(Expression::Lit { value: Literal::Char(c as u8), ty: None })),
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
            Ok(n) => Ok(Node::Expr(Expression::Lit { value: Literal::UInt64(n), ty: None })),
            Err(e) if e.kind() == &IntErrorKind::PosOverflow || e.kind() == &IntErrorKind::NegOverflow => {
                Err(ParseError::from((format!("Numeric literal out of integer range: {}", token), token)))
            },
            _ => match n.parse::<f32>() {
                Ok(n) => Ok(Node::Expr(Expression::Lit { value: Literal::Float(n), ty: None })),
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

        Ok(ast::Node::Expr(Expression::Lit { value: Literal::Array { elements, inner_ty: None }, ty: None }))
    }

    /// Misc productions

    // Prototype ::= 'fn' ident '(' ( TypedDecl ( ',' TypedDecl )* )* ')' ( '->' TypeAntn )? ;
    fn parse_proto(&mut self) -> Result<Prototype, ParseError> {
        let fn_name =
            expect_next_token!(self.tokens, TokenType::Ident(_), "Expecting function name in prototype");

        expect_next_token!(self.tokens, TokenType::OpenParen, "Expecting `(` in prototype");

        // Parse args list
        let mut args: Vec<(String, Type)> = vec![];
        while let Some(&next) = self.tokens.peek() {
            // Matches immediate ')'
            if next.tt == TokenType::CloseParen {
                break;
            }

            // Get the name of the argument and its type annotation
            let (name, antn) = self.parse_typed_decl("prototype")?;

            args.push((name.to_string(), antn));

            // This rustic mess checks for a ',' or a ')' in the argument
            // list. If one isn't found we try to create a new "error token"
            // with the right context for the error message. If the bad token is
            // an implicit semicolon, take the next one in the list or use EOF.
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
                None => unreachable!("Internal error: token can't be None in prototype"),
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

        Ok(Prototype::new(fn_name.to_string(), args, ret_type))
    }

    // VarInit ::= TypedDecl ( '=' Expr  )? ;
    fn parse_var_init(&mut self, caller: &str) -> Result<(String, Type, Option<Node>), ParseError> {
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
                let ty = expect_next_token!(
                    self.tokens,
                    TokenType::VarType(_),
                    format!("Expecting type after `[` in `{}` type annotation", caller)
                );
                expect_next_token!(
                    self.tokens,
                    TokenType::Semicolon(_),
                    format!("Expecting semicolon after `{}` in `{}` type annotation", ty, caller)
                );

                let size = match self.parse_expr(0)? {
                    Node::Expr(Expression::Lit { value: Literal::UInt64(s), .. }) => s,
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
                Type::Array(Box::new(ty.clone()), size.try_into().unwrap())
            },
            Some(Token { tt: TokenType::VarType(ty), .. }) => ty.clone(),
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
        // Ok(ty.clone())
        Ok(ty)
    }

    // TypedDecl ::= ident ':' TypeAntn ;
    fn parse_typed_decl(&mut self, caller: &str) -> Result<(String, Type), ParseError> {
        let err = match caller {
            "prototype" => format!("Expecting identifier or `)` in `{}` typed declaration", caller),
            _ => format!("Expecting identifier in `{}` typed declaration", caller),
        };

        let name = expect_next_token!(self.tokens, TokenType::Ident(_), err);

        expect_next_token!(
            self.tokens,
            TokenType::Colon,
            format!("Expecting `:` after identifier in `{}` typed declaration", caller)
        );
        Ok((name.to_owned(), self.parse_type_antn(caller)?))
    }

    // ExprList ::= Expr ','? | Expr ( ',' Expr )* ;
    fn parse_expr_list(&mut self, term: TokenType, in_err: &str) -> Result<Vec<Node>, ParseError> {
        let mut args: Vec<Node> = vec![];
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
