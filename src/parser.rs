use serde::Serialize;
use std::{fmt::Display, iter::Peekable, slice::Iter};

use crate::lexer::{Symbol, Token, TokenType};

macro_rules! expect_next_token {
    // Matches patterns like TokenType::Let
    ($ts:expr, $( $e:tt::$v:tt )|+ , $err:expr) => {
        let t = $ts.next();
        match t {
            $( Some(Token { tt: $e::$v, .. }) => (), )+
            _ => {
                return Err(ParseError::from((
                    format!(
                        "{}. Got {}",
                        $err.to_string(),
                        t.map_or(TokenType::Eof, |x| x.tt.clone())
                    ),
                    t.unwrap_or(&Token::default())
                )))
            }
        }
    };

    // Matches patterns like TokenType::Op(Symbol::Assign)
    ($ts:expr, $( $e:tt::$v:tt(Symbol::$s:tt) )|+ , $err:expr) => {
        let t = $ts.next();
        match t {
            $( Some(Token { tt: $e::$v(Symbol::$s), .. }) => (), )+
            _ => {
                return Err(ParseError::from((
                    format!(
                        "{}. Got {}",
                        $err.to_string(),
                        t.map_or(TokenType::Eof, |x| x.tt.clone())
                    ),
                    t.unwrap_or(&Token::default())
                )))
            }
        }
    };

    // Matches patterns like TokenType::Ident(_) and used for return value
    ($ts:expr, $t:tt::$v:tt($_:tt), $err:expr) => {
        {
            let t = $ts.next();
            match t {
                Some(Token { tt: $t::$v(t), .. }) => t,
                _ => {
                    return Err(ParseError::from((
                        format!(
                            "{}. Got {}",
                            $err.to_string(),
                            t.map_or(TokenType::Eof, |x| x.tt.clone())
                        ),
                        t.unwrap_or(&Token::default())
                    )))
                }
            }
        }
    };
}

// Matches token type and executes $and or returns None
macro_rules! token_is_and_then {
    ($to:expr, $tt:pat, $and:expr) => {
        match $to {
            Some(Token { tt: $tt, .. }) => $and,
            _ => None,
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
    fn bin_prec(op: Symbol) -> Result<OpPrec, String> {
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

    fn un_prec(op: Symbol) -> Result<u8, String> {
        use Symbol::*;
        match op {
            Not => Ok(9),
            Minus => Ok(8),
            x => Err(format!("Unknown unary operator: {}", x)),
        }
    }
}

#[derive(Debug, PartialEq, Serialize)]
pub struct ParseError {
    message: String,
    line: usize,
    column: usize,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut msg = format!("Parsing error: {}", self.message);

        if self.line != 0 && self.column != 0 {
            msg += &format!(" at {}:{}", self.line, self.column);
        }
        write!(f, "{}", msg)
    }
}

impl std::error::Error for ParseError {}

impl From<(String, &Token)> for ParseError {
    fn from((msg, t): (String, &Token)) -> Self {
        ParseError {
            message: msg,
            line: t.line,
            column: t.column,
        }
    }
}

impl From<String> for ParseError {
    fn from(msg: String) -> Self {
        ParseError {
            message: msg,
            line: 0,
            column: 0,
        }
    }
}

type ExprParseResult = Result<Expression, ParseError>;
type ProtoParseResult = Result<Prototype, ParseError>;
type FuncParseResult = Result<Function, ParseError>;

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
    pub fn parse(mut self) -> Result<Vec<AstNode>, ParseError> {
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

    // Parses arbitrary length binary and unary expressions. Uses Pratt with op
    // precedence parsing.
    fn parse_expression(&mut self, min_p: u8) -> ExprParseResult {
        // Consume token and load up lhs. These are all considered primary
        // expressions and are valid expression starters.
        //
        // TODO: for, let, if will likely become statements and need to be
        // removed.
        let token = self
            .tokens
            .next()
            .ok_or_else(|| "Invalid expression".to_string())?;
        let mut lhs = match &token.tt {
            TokenType::Int(n) => self.parse_num(*n)?,
            TokenType::Ident(id) => self.parse_ident(id)?,
            TokenType::OpenParen => self.parse_paren()?,
            TokenType::If => self.parse_cond()?,
            TokenType::For => self.parse_for()?,
            TokenType::Let => self.parse_let()?,
            TokenType::Op(sym) => {
                // Handle unary operators
                let p = OpPrec::un_prec(*sym)?;
                let rhs = self.parse_expression(p)?;
                Expression::UnOp {
                    sym: *sym,
                    rhs: Box::new(rhs),
                }
            }
            x => {
                return Err(ParseError::from((
                    format!("Expecting primary expression. Got {}", x),
                    token,
                )))
            }
        };

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
            lhs = self.parse_binop(sym, lhs, rhs).unwrap();
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

        let mut args: Vec<String> = vec![];
        while let Some(&next) = self.tokens.peek() {
            if next.tt == TokenType::CloseParen {
                break;
            }

            let id = expect_next_token!(
                self.tokens,
                TokenType::Ident(_),
                "Expecting ')' or identifier in prototype"
            );
            args.push(id.to_string());

            // XXX merge with below error?
            let next = self.tokens.peek().ok_or_else(|| {
                ParseError::from(("Expecting ',' or ')' in prototype".to_string(), next))
                    .to_string()
            })?;

            // XXX after all of the error refactoring, can we delete the if? (not if else)
            if next.tt == TokenType::CloseParen {
                break;
            } else if next.tt != TokenType::Comma {
                return Err(ParseError::from((
                    format!("Expecting ',' or ')' in prototype. Got {}", next),
                    *next,
                )));
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

    fn parse_num(&self, n: u64) -> ExprParseResult {
        Ok(Expression::Num { value: n })
    }

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

        // XXX is this the same as parse_proto?
        let mut args: Vec<Expression> = vec![];
        while let Some(next) = self.tokens.peek() {
            if next.tt == TokenType::CloseParen {
                break;
            }

            args.push(self.parse_expression(0)?);

            // XXX merge with below error?
            let &next = self
                .tokens
                .peek()
                .ok_or_else(|| "Expecting ',' or ')' in function call".to_string())?;

            if next.tt == TokenType::CloseParen {
                break;
            } else if next.tt != TokenType::Comma {
                return Err(ParseError::from((
                    format!("Expecting ',' in function call. Got {}", next),
                    next,
                )));
            }
            // Eat comma
            self.tokens.next();
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

    fn parse_binop(&self, sym: Symbol, lhs: Expression, rhs: Expression) -> ExprParseResult {
        Ok(Expression::BinOp {
            sym,
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

        let init = token_is_and_then!(self.tokens.peek(), TokenType::Op(Symbol::Assign), {
            self.tokens.next();
            Some(self.parse_expression(0)?)
        });

        Ok(Expression::Let {
            name: var_name.to_owned(),
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
