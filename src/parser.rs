use std::{fmt::Display, iter::Peekable, slice::Iter};

use crate::lexer::Token;

macro_rules! expect_next_token {
    ($ts:expr, $t:tt::$v:tt, $err:expr) => {
        match $ts.next() {
            Some(t @ $t::$v) => t,
            Some(_) | None => return Err($err.to_string()),
        }
    };

    ($ts:expr, $t:tt::$v:tt($_:tt), $err:expr) => {
        match $ts.next() {
            Some($t::$v(t)) => t,
            Some(_) | None => return Err($err.to_string()),
        }
    };
}

#[derive(Debug, PartialEq)]
pub enum Expression {
    Num {
        value: f64,
    },
    Var {
        name: String,
    },
    BinOp {
        op: char,
        lhs: Box<Expression>,
        rhs: Box<Expression>,
    },
    Call {
        name: String,
        args: Vec<Expression>,
    },
    Cond {
        cond: Box<Expression>,
        cons: Box<Expression>,
        alt: Option<Box<Expression>>,
    },
    For {
        var_name: String,
        start: Box<Expression>,
        cond: Box<Expression>,
        step: Box<Expression>,
        body: Vec<Expression>,
    },
}

impl Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expression::Num { value } => write!(f, "{}", value),
            Expression::BinOp { op, lhs, rhs } => write!(f, "({} {} {})", op, lhs, rhs),
            Expression::Var { name } => write!(f, "{}", name),
            Expression::Call { name, args } => {
                let mut s = format!("({}", name);
                if !args.is_empty() {
                    for arg in args {
                        s += &format!(" {}", arg);
                    }
                }
                write!(f, "{})", s)
            }
            Expression::Cond { cond, cons, alt } => {
                let mut s = format!("(if {} {}", cond, cons);
                if let Some(alt) = alt {
                    s += &format!(" {}", alt);
                }
                write!(f, "{})", s)
            }
            Expression::For {
                var_name,
                start,
                cond,
                step,
                body,
            } => {
                let mut s = format!("(for (let {} {}) {} {}", var_name, start, cond, step);
                s += &body.iter().fold(String::new(), |mut acc, n| {
                    acc += &format!(" {}", n);
                    acc
                });
                write!(f, "{})", s)
            }
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Prototype {
    pub name: String,
    pub args: Vec<String>,
}

impl Display for Prototype {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = format!("({}", self.name);
        if !self.args.is_empty() {
            for arg in &self.args {
                s += &format!(" {}", arg);
            }
        }
        write!(f, "{})", s)
    }
}

#[derive(Debug, PartialEq)]
pub struct Function {
    pub proto: Box<Prototype>,
    pub body: Option<Vec<Expression>>,
}

impl Display for Function {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.body {
            Some(body) if !body.is_empty() => {
                let s = body.iter().fold(String::new(), |mut acc, n| {
                    acc += &format!(" {}", n);
                    acc
                });
                write!(f, "(define {}{})", self.proto, s)
            }
            _ => write!(f, "(define {})", self.proto),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum AstNode {
    Expr(Expression),
    Proto(Prototype),
    Func(Function),
}

// Display functions allow us to convert to S-expressions for easier testing
impl Display for AstNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AstNode::Expr(expr) => write!(f, "{}", expr),
            AstNode::Proto(proto) => write!(f, "{}", proto),
            AstNode::Func(func) => write!(f, "{}", func),
        }
    }
}

enum OpPrec {
    Left(u8),
    Right(u8),
}

impl OpPrec {
    fn prec(op: char) -> Result<OpPrec, String> {
        match op {
            '^' => Ok(OpPrec::Right(4)),
            '*' | '/' => Ok(OpPrec::Left(3)),
            '+' | '-' => Ok(OpPrec::Left(2)),
            '>' | '<' => Ok(OpPrec::Left(1)),
            x => Err(format!("Unknown operator: {}", x)),
        }
    }
}

type ExprParseResult = Result<Expression, String>;
type ProtoParseResult = Result<Prototype, String>;
type FuncParseResult = Result<Function, String>;

pub struct Parser<'a> {
    ast: Vec<AstNode>,
    tokens: Peekable<Iter<'a, Token>>,
}

impl<'a> Parser<'a> {
    pub fn new(tokens: &'a [Token]) -> Self {
        Parser {
            ast: vec![],
            tokens: tokens.iter().peekable(),
        }
    }

    // Parse each token using recursive descent.
    pub fn parse(mut self) -> Result<Vec<AstNode>, String> {
        while let Some(t) = self.tokens.peek() {
            let node = match t {
                Token::Fn => AstNode::Func(self.parse_function()?),
                Token::Extern => AstNode::Func(self.parse_extern()?),
                _ => AstNode::Expr(self.parse_expression(0)?),
            };
            self.ast.push(node);
        }
        Ok(self.ast)
    }

    // Parses arbitrary length binary expressions. Uses Pratt with op precedence
    // parsing.
    fn parse_expression(&mut self, min_p: u8) -> ExprParseResult {
        // Consume token and load up lhs.
        let mut lhs = self.parse_primary()?;

        // Peek at the next token, otherwise return current lhs.
        while let Some(next) = self.tokens.peek() {
            // Should always be an operator after parse_primary().
            let op = match next {
                Token::Op(op) => op,
                // Start a new expression if we see two primaries in a row.
                _ => break,
            };

            // Determine operator precedence and associativity.
            // Stop eating and return the lhs if the current op:
            //   - is lower precedence than the last one (min_p), or:
            //   - is the same precedence and associates left
            let p = match OpPrec::prec(*op)? {
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

            // Advance past op.
            self.tokens.next();

            // Descend for rhs with the current precedence as min_p.
            let rhs = self.parse_expression(p)?;
            // Make a lhs and continue loop.
            lhs = self.parse_op(*op, lhs, rhs).unwrap();
        }
        Ok(lhs)
    }

    fn parse_function(&mut self) -> FuncParseResult {
        // Eat 'fn'
        self.tokens.next();

        let proto = self.parse_proto()?;
        expect_next_token!(self.tokens, Token::OpenBrace, "Expecting '{' in function definition");

        // If close brace, body is empty.
        let mut body: Vec<Expression> = vec![];
        if self.tokens.peek().is_some() {
            // XXX
            while let Some(t) = self.tokens.peek() {
                match t {
                    Token::CloseBrace => {
                        self.tokens.next();
                        break;
                    }
                    _ => body.push(self.parse_expression(0)?),
                }
            }
        } else {
            return Err("Expecting '}' in function definition".to_string());
        };

        let node = Function {
            proto: Box::new(proto),
            body: Some(body),
        };

        Ok(node)
    }

    fn parse_extern(&mut self) -> FuncParseResult {
        // Eat 'extern'
        self.tokens.next();

        let proto = self.parse_proto()?;
        Ok(Function {
            proto: Box::new(proto),
            body: None,
        })
    }

    fn parse_proto(&mut self) -> ProtoParseResult {
        let fn_name = expect_next_token!(self.tokens, Token::Ident(_), "Expecting function name");
        expect_next_token!(self.tokens, Token::OpenParen, "Expecting '(' in prototype");

        let mut args: Vec<String> = vec![];
        while let Some(&next) = self.tokens.peek() {
            if *next == Token::CloseParen {
                break;
            }

            let id = expect_next_token!(self.tokens, Token::Ident(_), "Expecting identifier in prototype");
            args.push(id.to_string());

            let &next = self
                .tokens
                .peek()
                .ok_or_else(|| "Premature end. Expecting ',' or ')'.".to_string())?;

            if *next == Token::CloseParen {
                break;
            } else if *next != Token::Comma {
                return Err(format!("Expecting ','. Got: {}", next));
            }
            // Eat comma
            self.tokens.next();
        }

        // Eat close paren
        self.tokens.next();

        Ok(Prototype {
            name: fn_name.to_string(),
            args,
        })
    }

    // Returns primary expression
    fn parse_primary(&mut self) -> ExprParseResult {
        let node = if let Some(t) = self.tokens.next() {
            match t {
                Token::Int(n) => self.parse_num(*n),
                Token::Ident(id) => self.parse_ident(id),
                Token::OpenParen => self.parse_paren(),
                Token::If => self.parse_cond(),
                Token::For => self.parse_for(),
                x => return Err(format!("Expecting primary expression. Got: {}", x)),
            }
        } else {
            unreachable!("parse_primary()");
        };
        node
    }

    fn parse_num(&self, n: f64) -> ExprParseResult {
        Ok(Expression::Num { value: n })
    }

    fn parse_ident(&mut self, id: &str) -> ExprParseResult {
        let node = Expression::Var {
            name: id.to_owned(),
        };

        // If next is not a '(', the current token is just a simple var.
        match self.tokens.peek() {
            Some(t @ Token::OpenParen) => t,
            Some(_) | None => return Ok(node),
        };

        // Eat open paren
        self.tokens.next();

        let mut args: Vec<Expression> = vec![];
        while let Some(&next) = self.tokens.peek() {
            if *next == Token::CloseParen {
                break;
            }

            args.push(self.parse_expression(0)?);

            let &next = self
                .tokens
                .peek()
                .ok_or_else(|| "Premature end. Expecting ',' or ')'.".to_string())?;

            if *next == Token::CloseParen {
                break;
            } else if *next != Token::Comma {
                return Err(format!("Expecting ','. Got: {}", next));
            }
            // Eat comma
            self.tokens.next();
        }

        // Eat close paren
        self.tokens.next();

        Ok(Expression::Call {
            name: id.to_owned(),
            args,
        })
    }

    fn parse_op(&self, op: char, lhs: Expression, rhs: Expression) -> ExprParseResult {
        Ok(Expression::BinOp {
            op,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        })
    }

    fn parse_paren(&mut self) -> ExprParseResult {
        let lhs = self.parse_expression(0);
        self.tokens.next(); // Eat ')'
        lhs
    }

    fn parse_cond(&mut self) -> ExprParseResult {
        let cond = self.parse_expression(0)?;
        expect_next_token!(self.tokens, Token::OpenBrace, "Expecting '{' after conditional");

        let cons = self.parse_expression(0)?;
        expect_next_token!(self.tokens, Token::CloseBrace, "Expecting '}' after consequent");

        let alt = match self.tokens.peek() {
            Some(Token::Else) => {
                self.tokens.next(); // Eat else
                expect_next_token!(self.tokens, Token::OpenBrace, "Expecting '{' after conditional");
                let alt = Some(self.parse_expression(0)?);
                expect_next_token!(self.tokens, Token::CloseBrace, "Expecting '}' after consequent");
                alt
            }
            _ => None,
        };

        Ok(Expression::Cond {
            cond: Box::new(cond),
            cons: Box::new(cons),
            alt: alt.map(Box::new),
        })
    }

    fn parse_for(&mut self) -> ExprParseResult {
        expect_next_token!(self.tokens, Token::Let, "Expecting 'let' after for");

        let var_name = expect_next_token!(self.tokens, Token::Ident(_), "Expecting identifier after let");
        expect_next_token!(self.tokens, Token::Assign, "Expecting '=' after identifer");

        let start = self.parse_expression(0)?;
        expect_next_token!(self.tokens, Token::Semicolon, "Expecting ';' after start");

        let cond = self.parse_expression(0)?;
        expect_next_token!(self.tokens, Token::Semicolon, "Expecting ';' after condition");

        let step = self.parse_expression(0)?;
        expect_next_token!(self.tokens, Token::OpenBrace, "Expecting '{' after step".to_string());

        let mut body: Vec<Expression> = vec![];
        while let Some(t) = self.tokens.peek() {
            match t {
                Token::CloseBrace => {
                    self.tokens.next();
                    break;
                }
                _ => body.push(self.parse_expression(0)?),
            }
        }

        Ok(Expression::For {
            var_name: var_name.to_owned(),
            start: Box::new(start),
            cond: Box::new(cond),
            step: Box::new(step),
            body,
        })
    }
}
