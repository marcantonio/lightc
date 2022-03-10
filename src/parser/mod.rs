use std::{iter::Peekable, slice::Iter};

use self::{errors::ParseError, precedence::OpPrec};
use crate::ast::{AstNode, Expression, Function, Prototype};
use crate::token::{Symbol, Token, TokenType, Type};

#[macro_use]
mod macros;
mod errors;
mod precedence;

type ExprParseResult = Result<Expression, ParseError>;
type ProtoParseResult = Result<Prototype, ParseError>;
type FuncParseResult = Result<Function, ParseError>;

pub(crate) struct Parser<'a> {
    ast: Vec<AstNode>,
    tokens: Peekable<Iter<'a, Token>>,
}

impl<'a> Parser<'a> {
    pub(crate) fn new(tokens: &'a [Token]) -> Self {
        Parser {
            ast: vec![],
            tokens: tokens.iter().peekable(),
        }
    }

    // Parse each token using recursive descent
    pub(crate) fn parse(mut self) -> Result<Vec<AstNode>, ParseError> {
        while let Some(t) = self.tokens.peek() {
            let node = match t.tt {
                TokenType::Fn => AstNode::Func(self.parse_function()?),
                TokenType::Extern => AstNode::Func(self.parse_extern()?),
                _ => AstNode::Expr(self.parse_expression(0)?),
            };
            self.ast.push(node);
        }
        Ok(self.ast)
    }

    // Consume token and dispatch. These are all considered primary
    // expressions and are valid expression starters.
    //
    // TODO: for, let, if will likely become statements and need to be
    // removed.
    fn parse_primary(&mut self) -> ExprParseResult {
        let token = self
            .tokens
            .next()
            .ok_or_else(|| "Premature end of expression".to_string())?;

        match &token.tt {
            TokenType::Num(num) => self.parse_num(num, token),
            TokenType::Ident(id) => self.parse_ident(id),
            TokenType::OpenParen => self.parse_paren(),
            TokenType::If => self.parse_cond(),
            TokenType::For => self.parse_for(),
            TokenType::Let => self.parse_let(),
            TokenType::Op(sym) => self.parse_unop(*sym),
            x => {
                return Err(ParseError::from((
                    format!("Expecting primary expression. Got {}", x),
                    token,
                )))
            }
        }
    }

    // Parses arbitrary length binary expressions. Uses Pratt with op
    // precedence parsing.
    fn parse_expression(&mut self, min_p: u8) -> ExprParseResult {
        // Load up lhs with a primary
        let mut lhs = self.parse_primary()?;

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
            // Make a lhs and continue loop
            lhs = Expression::BinOp {
                sym,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            };
        }
        Ok(lhs)
    }

    fn parse_unop(&mut self, sym: Symbol) -> ExprParseResult {
        let p = OpPrec::un_prec(sym)?;
        let rhs = self.parse_expression(p)?;
        Ok(Expression::UnOp {
            sym,
            rhs: Box::new(rhs),
        })
    }

    fn parse_function(&mut self) -> FuncParseResult {
        // Eat 'fn'
        self.tokens.next();

        Ok(Function {
            proto: Box::new(self.parse_proto()?),
            body: Some(self.parse_block()?),
        })
    }

    fn parse_extern(&mut self) -> FuncParseResult {
        // Eat 'extern'
        self.tokens.next();

        Ok(Function {
            proto: Box::new(self.parse_proto()?),
            body: None,
        })
    }

    fn parse_proto(&mut self) -> ProtoParseResult {
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

            expect_next_token!(
                self.tokens,
                TokenType::Colon,
                "Expecting ':' in prototype"
            );

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

    fn parse_num(&self, num: &str, token: &Token) -> ExprParseResult {
        // if let Ok(n) = num.parse::<i64>() {
        //     Ok(Expression::I64(n))
        if let Ok(n) = num.parse::<u64>() {
            Ok(Expression::U64(n))
        } else if let Ok(n) = num.parse::<f64>() {
            Ok(Expression::F64(n))
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
    fn parse_ident(&mut self, id: &str) -> ExprParseResult {
        let node = Expression::Var {
            name: id.to_owned(),
        };

        // If next is not a '(', the current token is just a simple var
        match self.tokens.peek() {
            Some(Token {
                tt: TokenType::OpenParen,
                ..
            }) => (),
            _ => return Ok(node),
        };

        // Eat open paren
        self.tokens.next();

        let mut args: Vec<Expression> = vec![];
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

        Ok(Expression::Call {
            name: id.to_owned(),
            args,
        })
    }

    fn parse_paren(&mut self) -> ExprParseResult {
        let lhs = self.parse_expression(0);
        self.tokens.next(); // Eat ')'
        lhs
    }

    fn parse_cond(&mut self) -> ExprParseResult {
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

        Ok(Expression::Cond {
            cond: Box::new(cond),
            cons,
            alt,
        })
    }

    fn parse_for(&mut self) -> ExprParseResult {
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

        Ok(Expression::For {
            var_name: var_name.to_owned(),
            start: Box::new(start),
            cond: Box::new(cond),
            step: Box::new(step),
            body: self.parse_block()?,
        })
    }

    fn parse_let(&mut self) -> ExprParseResult {
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

        Ok(Expression::Let {
            name: var_name.to_owned(),
            ty: *ty,
            init: init.map(Box::new),
        })
    }

    // Helper to collect a bunch of expressions enclosed by braces into a Vec<T>
    fn parse_block(&mut self) -> Result<Vec<Expression>, ParseError> {
        let mut block: Vec<Expression> = vec![];

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
                _ => block.push(self.parse_expression(0)?),
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
        lexer::Lexer,
        parser::{AstNode, ParseError, Parser},
    };

    fn ast_to_string(ast: Result<&[AstNode], &ParseError>) -> String {
        match ast {
            Ok(ast) => ast.iter().map(|x| x.to_string()).collect(),
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
                        let ast_string = ast_to_string(ast.as_deref());
                        (ast, ast_string)
                    })
                    .collect::<Vec<_>>();
                assert_yaml_snapshot!(asts);
            });
        });
    }
}
