use std::{iter::Peekable, slice::Iter};

use self::{errors::ParseError, precedence::OpPrec};
use crate::ast::{Ast, Expression, Node, Prototype, Statement};
use crate::token::{Symbol, Token, TokenType, Type};

#[macro_use]
mod macros;
mod errors;
mod precedence;

type ParseResult = Result<Node, ParseError>;

pub(crate) struct Parser<'a> {
    ast: Ast<Node>,
    tokens: Peekable<Iter<'a, Token>>,
}

impl<'a> Parser<'a> {
    pub(crate) fn new(tokens: &'a [Token]) -> Self {
        Parser {
            ast: Ast::new(),
            tokens: tokens.iter().peekable(),
        }
    }

    // Parse each token using recursive descent
    pub(crate) fn parse(mut self) -> Result<Ast<Node>, ParseError> {
        while let Some(t) = self.tokens.peek() {
            let node = match t.tt {
                //_ => AstNode::Expr(self.parse_expression(0)?),
                _ => self.parse_statement()?,
            };
            self.ast.add(node);
        }
        Ok(self.ast)
    }

    fn parse_statement(&mut self) -> ParseResult {
        let token = self
            .tokens
            .peek()
            .ok_or_else(|| "Premature end of statement".to_string())?;

        let expr = match &token.tt {
            TokenType::If => self.parse_cond()?,
            TokenType::For => self.parse_for()?,
            TokenType::Let => self.parse_let()?,
            TokenType::Fn => self.parse_function()?,
            TokenType::Extern => self.parse_extern()?,
            _ => self.parse_expression(0)?,
        };
        Ok(expr)
    }

    // Consume token and dispatch. These are all considered primary expressions.
    //
    // TODO: for, let, if will likely become statements and need to be removed.
    fn parse_expression(&mut self, min_p: u8) -> ParseResult {
        let token = self
            .tokens
            .next()
            .ok_or_else(|| "Premature end of expression".to_string())?;

        let expr = match &token.tt {
            TokenType::Num(num) => self.parse_num(num, token)?,
            TokenType::Ident(id) => self.parse_ident(id)?,
            TokenType::OpenParen => self.parse_paren()?,
            TokenType::Op(sym) => self.parse_unop(*sym)?,
            x => {
                return Err(ParseError::from((
                    format!("Expecting primary expression. Got {}", x),
                    token,
                )))
            }
        };

        // Check for binop and process or return
        self.parse_binop(expr, min_p)
    }

    // Parses arbitrary length binary expressions. Uses Pratt with op
    // precedence parsing.
    fn parse_binop(&mut self, mut lhs: Node, min_p: u8) -> ParseResult {
        // Peek at the next token, otherwise return current lhs
        while let Some(next) = self.tokens.peek() {
            // Should always be an operator after a primary
            let sym = match next.tt {
                TokenType::Op(s) => s,
                // Start a new expression if we see two primaries in a row
                _ => break,
            };

            // Determine operator precedence and associativity.
            // Stop eating and return the lhs if the current op:
            //   - is lower precedence than the last one (min_p), or:
            //   - is the same precedence and associates left
            let p = match OpPrec::bin_prec(sym)? {
                OpPrec::Left(p) => {
                    if p <= min_p {
                        break;
                    }
                    p
                }
                OpPrec::Right(p) => {
                    if p < min_p {
                        break;
                    }
                    p
                }
            };

            // Advance past op
            self.tokens.next();

            // Descend for rhs with the current precedence as min_p
            let rhs = self.parse_expression(p)?;
            // Make a new lhs and continue loop
            lhs = Node::Expr(Expression::BinOp {
                sym,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            });
        }
        Ok(lhs)
    }

    fn parse_unop(&mut self, sym: Symbol) -> ParseResult {
        let p = OpPrec::un_prec(sym)?;
        let rhs = self.parse_expression(p)?;
        Ok(Node::Expr(Expression::UnOp {
            sym,
            rhs: Box::new(rhs),
        }))
    }

    fn parse_function(&mut self) -> ParseResult {
        // Eat 'fn'
        self.tokens.next();

        Ok(Node::Stmt(Statement::Fn {
            proto: Box::new(self.parse_proto()?),
            body: Some(self.parse_block()?),
        }))
    }

    fn parse_extern(&mut self) -> ParseResult {
        // Eat 'extern'
        self.tokens.next();

        Ok(Node::Stmt(Statement::Fn {
            proto: Box::new(self.parse_proto()?),
            body: None,
        }))
    }

    fn parse_proto(&mut self) -> Result<Prototype, ParseError> {
        let fn_name = expect_next_token!(
            self.tokens,
            TokenType::Ident(_),
            "Expecting function name in prototype"
        );

        expect_next_token!(
            self.tokens,
            TokenType::OpenParen,
            "Expecting '(' in prototype"
        );

        let mut args: Vec<(String, Type)> = vec![];
        while let Some(&next) = self.tokens.peek() {
            // Matches immediate ')'
            if next.tt == TokenType::CloseParen {
                break;
            }

            let id = expect_next_token!(
                self.tokens,
                TokenType::Ident(_),
                "Expecting ')' or identifier in prototype"
            );

            expect_next_token!(self.tokens, TokenType::Colon, "Expecting ':' in prototype");

            let ty = expect_next_token!(
                self.tokens,
                TokenType::VarType(_),
                "Expecting vartype in prototype"
            );

            args.push((id.to_string(), *ty));

            match self.tokens.peek() {
                Some(Token {
                    tt: TokenType::CloseParen,
                    ..
                }) => break,
                Some(Token {
                    tt: TokenType::Comma,
                    ..
                }) => self.tokens.next(), // Eat comma
                Some(x) => {
                    return Err(ParseError::from((
                        format!("Expecting ',' or ')' in prototype. Got {}", x),
                        *x,
                    )))
                }
                None => {
                    return Err(ParseError::from(String::from(
                        "Expecting one of [',', ')', ':']. Got EOF",
                    )))
                }
            };
        }

        // Eat close paren
        self.tokens.next();

        Ok(Prototype {
            name: fn_name.to_string(),
            args,
        })
    }

    fn parse_num(&self, num: &str, token: &Token) -> ParseResult {
        // if let Ok(n) = num.parse::<i64>() {
        //     Ok(Expression::I64(n))
        if let Ok(n) = num.parse::<u64>() {
            Ok(Node::Expr(Expression::U64(n)))
        } else if let Ok(n) = num.parse::<f64>() {
            Ok(Node::Expr(Expression::F64(n)))
        } else {
            Err(ParseError::from((
                format!("Invalid number literal: {}", token),
                token,
            )))
        }
    }

    // pub(crate) fn bool(s: &str) -> Option<Value> {
    //     match s.parse::<bool>() {
    //         Ok(b) => Some(Value::Bool(b)),
    //         Err(_) => None,
    //     }
    // }        Ok(Expression::Num { value: n })

    // Variable or function call
    fn parse_ident(&mut self, id: &str) -> ParseResult {
        let node = Expression::Ident {
            name: id.to_owned(),
        };

        // If next is not a '(', the current token is just a simple var
        match self.tokens.peek() {
            Some(Token {
                tt: TokenType::OpenParen,
                ..
            }) => (),
            _ => return Ok(Node::Expr(node)),
        };

        // Eat open paren
        self.tokens.next();

        let mut args: Vec<Node> = vec![];
        while let Some(&next) = self.tokens.peek() {
            // Matches immediate ')'
            if next.tt == TokenType::CloseParen {
                break;
            }

            args.push(self.parse_expression(0)?);

            match self.tokens.peek() {
                Some(Token {
                    tt: TokenType::CloseParen,
                    ..
                }) => break,
                Some(Token {
                    tt: TokenType::Comma,
                    ..
                }) => self.tokens.next(), // Eat comma
                _ => {
                    return Err(ParseError::from((
                        format!("Expecting ',' or ')' in function call. Got {}", next),
                        next,
                    )))
                }
            };
        }

        // Eat close paren
        expect_next_token!(
            self.tokens,
            TokenType::CloseParen,
            "Expecting ')' in function call"
        );

        Ok(Node::Expr(Expression::Call {
            name: id.to_owned(),
            args,
        }))
    }

    fn parse_paren(&mut self) -> ParseResult {
        let lhs = self.parse_expression(0);
        self.tokens.next(); // Eat ')'
        lhs
    }

    fn parse_cond(&mut self) -> ParseResult {
        self.tokens.next(); // Eat if

        let cond = self.parse_expression(0)?;
        let cons = self.parse_block()?;

        let alt = token_is_and_then!(self.tokens.peek(), TokenType::Else, {
            self.tokens.next(); // Eat else

            // To support `else if`, peek to check for `{` or `if`
            let next = self.tokens.peek();
            if matches!(next, Some(t) if t.tt != TokenType::If && t.tt != TokenType::OpenBrace) {
                return Err(ParseError::from((
                    "Expecting 'if' or '{' after else".to_string(),
                    *next.unwrap(),
                )));
            }

            let alt = self.parse_block()?;

            Some(alt)
        });

        Ok(Node::Stmt(Statement::Cond {
            cond: Box::new(cond),
            cons,
            alt,
        }))
    }

    fn parse_for(&mut self) -> ParseResult {
        self.tokens.next(); // Eat for

        // TODO: call parse_let() here
        expect_next_token!(self.tokens, TokenType::Let, "Expecting 'let' after for");

        let var_name = expect_next_token!(
            self.tokens,
            TokenType::Ident(_),
            "Expecting identifier after let"
        );
        expect_next_token!(
            self.tokens,
            TokenType::Op(Symbol::Assign),
            "Expecting '=' after identifer"
        );

        let start = self.parse_expression(0)?;
        expect_next_token!(
            self.tokens,
            TokenType::Semicolon,
            "Expecting ';' after start"
        );

        let cond = self.parse_expression(0)?;
        expect_next_token!(
            self.tokens,
            TokenType::Semicolon,
            "Expecting ';' after condition"
        );

        let step = self.parse_expression(0)?;

        Ok(Node::Stmt(Statement::For {
            var_name: var_name.to_owned(),
            start: Box::new(start),
            cond: Box::new(cond),
            step: Box::new(step),
            body: self.parse_block()?,
        }))
    }

    fn parse_let(&mut self) -> ParseResult {
        self.tokens.next(); // Eat let

        let var_name = expect_next_token!(
            self.tokens,
            TokenType::Ident(_),
            "Expecting identifier after let"
        );

        expect_next_token!(
            self.tokens,
            TokenType::Colon,
            "Expecting colon in let statement"
        );

        let ty = expect_next_token!(
            self.tokens,
            TokenType::VarType(_),
            "Type annotation required in let statement"
        );

        let init = token_is_and_then!(self.tokens.peek(), TokenType::Op(Symbol::Assign), {
            self.tokens.next();
            Some(self.parse_expression(0)?)
        });

        Ok(Node::Stmt(Statement::Let {
            name: var_name.to_owned(),
            ty: *ty,
            init: init.map(Box::new),
        }))
    }

    // Helper to collect a bunch of expressions enclosed by braces into a Vec<T>
    fn parse_block(&mut self) -> Result<Vec<Node>, ParseError> {
        let mut block: Vec<Node> = vec![];

        expect_next_token!(
            self.tokens,
            TokenType::OpenBrace,
            "Expecting '{' to start block"
        );

        while let Some(t) = self.tokens.peek() {
            match t.tt {
                TokenType::CloseBrace => {
                    self.tokens.next();
                    return Ok(block);
                }
                _ => block.push(self.parse_statement()?),
            }
        }

        // TODO: Could add more context here with some refactor
        Err(ParseError::from(
            "Expecting '}' to terminate block".to_string(),
        ))
    }
}

#[cfg(test)]
mod test {
    use insta::{assert_yaml_snapshot, glob, with_settings};
    use std::{
        fs::File,
        io::{BufRead, BufReader},
    };

    use crate::{
        ast::{Ast, Node},
        lexer::Lexer,
        parser::{ParseError, Parser},
    };

    fn ast_to_string(ast: Result<&Ast<Node>, &ParseError>) -> String {
        match ast {
            Ok(ast) => ast.nodes().iter().map(|x| x.to_string()).collect(),
            Err(err) => err.to_string(),
        }
    }

    #[test]
    fn test_parser() {
        with_settings!({ snapshot_path => "tests/snapshots", prepend_module_to_snapshot => false }, {
            glob!("tests/inputs/*.input", |path| {
                let file = File::open(path).expect("Error reading input file");
                let reader = BufReader::new(file);

                // Each line of the input files is meant to be a separate test
                // case. Treat each as its own AST. Including `ast_string` in the
                // output makes it more readable.
                let asts = reader
                    .lines()
                    .map(|line| {
                        let line = line.expect("Error reading input line");
                        let tokens = Lexer::new(&line).collect::<Result<Vec<_>, _>>().unwrap();
                        let ast = Parser::new(&tokens).parse();
                        let ast_string = ast_to_string(ast.as_ref());
                        (ast, ast_string)
                    })
                    .collect::<Vec<_>>();
                assert_yaml_snapshot!(asts);
            });
        });
    }
}
