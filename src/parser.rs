use serde::Serialize;
use std::{fmt::Display, iter::Peekable, slice::Iter};

use crate::lexer::{Symbol, Token};

macro_rules! expect_next_token {
    // Matches patterns like Token::Let
    ($ts:expr, $( $e:tt::$v:tt )|+ , $err:expr) => {
        match $ts.next() {
            $( Some(t @ $e::$v) => t, )+
            Some(_) | None => return Err($err.to_string()),
        }
    };

    // Matches patterns like Token::Op(Symbol::Assign)
    ($ts:expr, $( $e:tt::$v:tt(Symbol::$s:tt) )|+ , $err:expr) => {
        match $ts.next() {
            $( Some(t @ $e::$v(Symbol::$s)) => t, )+
            Some(_) | None => return Err($err.to_string()),
        }
    };

    // Matches patterns like Token::Ident(_) and used for return value
    ($ts:expr, $t:tt::$v:tt($_:tt), $err:expr) => {
        match $ts.next() {
            Some($t::$v(t)) => t,
            Some(_) | None => return Err($err.to_string()),
        }
    };
}

#[derive(Debug, PartialEq, Serialize)]
pub enum Expression {
    Num {
        value: u64,
    },
    Var {
        name: String,
    },
    BinOp {
        sym: Symbol,
        lhs: Box<Expression>,
        rhs: Box<Expression>,
    },
    UnOp {
        sym: Symbol,
        rhs: Box<Expression>,
    },
    Call {
        name: String,
        args: Vec<Expression>,
    },
    Cond {
        cond: Box<Expression>,
        cons: Vec<Expression>,
        alt: Option<Vec<Expression>>,
    },
    For {
        var_name: String,
        start: Box<Expression>,
        cond: Box<Expression>,
        step: Box<Expression>,
        body: Vec<Expression>,
    },
    Let {
        name: String,
        init: Option<Box<Expression>>,
    },
}

#[derive(Debug, PartialEq, Serialize)]
pub struct Prototype {
    pub name: String,
    pub args: Vec<String>,
}

#[derive(Debug, PartialEq, Serialize)]
pub struct Function {
    pub proto: Box<Prototype>,
    pub body: Option<Vec<Expression>>,
}

#[derive(Debug, PartialEq, Serialize)]
pub enum AstNode {
    Expr(Expression),
    Proto(Prototype),
    Func(Function),
}

enum OpPrec {
    Left(u8),
    Right(u8),
}

impl OpPrec {
    fn bin_prec(op: &Symbol) -> Result<OpPrec, String> {
        use Symbol::*;
        match op {
            Pow => Ok(OpPrec::Right(8)),
            Mult | Div => Ok(OpPrec::Left(7)),
            Plus | Minus => Ok(OpPrec::Left(6)),
            Gt | Lt => Ok(OpPrec::Left(5)),
            Eq => Ok(OpPrec::Left(4)),
            And => Ok(OpPrec::Left(3)),
            Assign => Ok(OpPrec::Left(2)),
            Or => Ok(OpPrec::Left(1)),
            x => Err(format!("Unknown binary operator: {}", x)),
        }
    }

    fn un_prec(op: &Symbol) -> Result<u8, String> {
        use Symbol::*;
        match op {
            Not => Ok(9),
            Minus => Ok(8),
            x => Err(format!("Unknown unary operator: {}", x)),
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

    // Parse each token using recursive descent
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

    // Parses arbitrary length binary and unary expressions. Uses Pratt with op
    // precedence parsing.
    fn parse_expression(&mut self, min_p: u8) -> ExprParseResult {
        // Consume token and load up lhs
        let token = self.tokens.next().ok_or("No LHS in expression?")?;
        let mut lhs = match token {
            // Handle unary operators
            Token::Op(sym) => {
                let p = OpPrec::un_prec(sym)?;
                let rhs = self.parse_expression(p)?;
                Expression::UnOp {
                    sym: *sym,
                    rhs: Box::new(rhs),
                }
            }
            t => self.parse_primary(t)?,
        };

        // Peek at the next token, otherwise return current lhs.
        while let Some(next) = self.tokens.peek() {
            // Should always be an operator after parse_primary().
            let sym = match next {
                Token::Op(s) => s,
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
            lhs = self.parse_op(sym, lhs, rhs).unwrap();
        }
        Ok(lhs)
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
        let fn_name = expect_next_token!(self.tokens, Token::Ident(_), "Expecting function name");
        expect_next_token!(self.tokens, Token::OpenParen, "Expecting '(' in prototype");

        let mut args: Vec<String> = vec![];
        while let Some(&next) = self.tokens.peek() {
            if *next == Token::CloseParen {
                break;
            }

            let id = expect_next_token!(
                self.tokens,
                Token::Ident(_),
                "Expecting identifier in prototype"
            );
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
    // XXX is this really needed?
    fn parse_primary(&mut self, token: &Token) -> ExprParseResult {
        match token {
            Token::Int(n) => self.parse_num(*n),
            Token::Ident(id) => self.parse_ident(id),
            Token::OpenParen => self.parse_paren(),
            Token::If => self.parse_cond(),
            Token::For => self.parse_for(),
            Token::Let => self.parse_let(),
            x => return Err(format!("Expecting primary expression. Got: {}", x)),
        }
    }

    fn parse_num(&self, n: u64) -> ExprParseResult {
        Ok(Expression::Num { value: n })
    }

    fn parse_ident(&mut self, id: &str) -> ExprParseResult {
        let node = Expression::Var {
            name: id.to_owned(),
        };

        // If next is not a '(', the current token is just a simple var
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

    fn parse_op(&self, sym: &Symbol, lhs: Expression, rhs: Expression) -> ExprParseResult {
        Ok(Expression::BinOp {
            sym: *sym,
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

        let cons = self.parse_block()?;

        let alt = match self.tokens.peek() {
            Some(Token::Else) => {
                self.tokens.next(); // Eat else

                // To support `else if`, peek to check for `{` or `if`
                if matches!(self.tokens.peek(), Some(&t) if *t != Token::If && *t != Token::OpenBrace) {
                    return Err("Expecting 'if' or '{' after else".to_string());
                }

                let alt = self.parse_block()?;

                Some(alt)
            }
            _ => None,
        };

        Ok(Expression::Cond {
            cond: Box::new(cond),
            cons,
            alt,
        })
    }

    fn parse_for(&mut self) -> ExprParseResult {
        expect_next_token!(self.tokens, Token::Let, "Expecting 'let' after for");

        let var_name = expect_next_token!(
            self.tokens,
            Token::Ident(_),
            "Expecting identifier after let"
        );
        expect_next_token!(
            self.tokens,
            Token::Op(Symbol::Assign),
            "Expecting '=' after identifer"
        );

        let start = self.parse_expression(0)?;
        expect_next_token!(self.tokens, Token::Semicolon, "Expecting ';' after start");

        let cond = self.parse_expression(0)?;
        expect_next_token!(
            self.tokens,
            Token::Semicolon,
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
            Token::Ident(_),
            "Expecting identifier after let"
        );

        let init = match self.tokens.peek() {
            Some(Token::Op(Symbol::Assign)) => {
                self.tokens.next();
                Some(self.parse_expression(0)?)
            }
            Some(_) | None => None,
        };

        Ok(Expression::Let {
            name: var_name.to_owned(),
            init: init.map(Box::new),
        })
    }

    // Helper to collect a bunch of expressions enclosed by braces into a Vec<T>
    fn parse_block(&mut self) -> Result<Vec<Expression>, String> {
        let mut block: Vec<Expression> = vec![];

        expect_next_token!(
            self.tokens,
            Token::OpenBrace,
            "Expecting '{' to start block"
        );

        while let Some(t) = self.tokens.peek() {
            match t {
                Token::CloseBrace => {
                    self.tokens.next();
                    return Ok(block);
                }
                _ => block.push(self.parse_expression(0)?),
            }
        }

        Err("Expecting '}' to terminate block".to_string())
    }
}

// Display functions allow us to convert to s-expressions for easier testing

impl Display for AstNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AstNode::Expr(expr) => write!(f, "{}", expr),
            AstNode::Proto(proto) => write!(f, "{}", proto),
            AstNode::Func(func) => write!(f, "{}", func),
        }
    }
}

impl Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expression::Num { value } => write!(f, "{}", value),
            Expression::BinOp { sym, lhs, rhs } => write!(f, "({} {} {})", sym, lhs, rhs),
            Expression::UnOp { sym, rhs } => write!(f, "({} {})", sym, rhs),
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
                let mut s = format!("(if {}", cond);
                s += &cons.iter().fold(String::new(), |mut acc, n| {
                    acc += &format!(" {}", n);
                    acc
                });

                if let Some(alt) = alt {
                    s += &alt.iter().fold(String::new(), |mut acc, n| {
                        acc += &format!(" {}", n);
                        acc
                    });
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
            Expression::Let { name, init: body } => {
                let mut s = format!("(let {}", name);
                if let Some(body) = body {
                    s += &format!(" {}", body);
                }
                write!(f, "{})", s)
            }
        }
    }
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
