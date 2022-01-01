use std::fmt::Display;

/// lexer ///

#[derive(Debug, PartialEq)]
pub enum Token {
    Fn,
    Let,
    OpenParen,
    CloseParen,
    OpenBrace,
    CloseBrace,
    Comma,
    Colon,
    Assign,
    Ident(String),
    Int(u64),
    VarType(Type),
    Op(char),
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Debug, PartialEq)]
pub enum Type {
    U64,
}

#[derive(Debug, PartialEq)]
pub enum LexError {
    InvalidNum,
}

pub type LexResult = std::result::Result<Vec<Token>, LexError>;

pub fn lexer(input: &str) -> LexResult {
    let mut tokens = vec![];

    // Main loop; one char at a time
    let mut stream: Vec<char> = input.chars().rev().collect();
    'main: while let Some(cur) = stream.pop() {
        // Ignore whitespace
        if cur.is_ascii_whitespace() {
            while let Some(c) = stream.pop() {
                if !c.is_ascii_whitespace() {
                    stream.push(c);
                    break;
                }
            }
        }

        // Comments
        if cur == '/' && stream.last() == Some(&'/') {
            while let Some(c) = stream.pop() {
                if c == '\n' {
                    continue 'main;
                }
            }
        }

        // Identifiers: keywords, function names, and variables
        if cur.is_ascii_alphabetic() {
            let mut identifier = String::from(cur);
            while let Some(c) = stream.pop() {
                if c.is_ascii_alphanumeric() {
                    identifier.push(c);
                } else {
                    stream.push(c);
                    break;
                }
            }

            tokens.push(match identifier.as_str() {
                "fn" => Token::Fn,
                "let" => Token::Let,
                "u64" => Token::VarType(Type::U64),
                _ => Token::Ident(identifier),
            })
        }

        // Numbers
        if cur.is_ascii_digit() {
            let mut num = String::from(cur);
            while let Some(c) = stream.pop() {
                if c.is_ascii_alphanumeric() {
                    num.push(c);
                } else {
                    stream.push(c);
                    break;
                }
            }

            tokens.push(match num.parse() {
                Ok(n) => Token::Int(n),
                Err(_) => return Err(LexError::InvalidNum),
            });
        }

        // Everything else
        if cur == '+' || cur == '-' || cur == '*' || cur == '/' || cur == '^' {
            tokens.push(Token::Op(cur));
        } else if cur == '=' {
            tokens.push(Token::Assign);
        } else if cur == ':' {
            tokens.push(Token::Colon);
        } else if cur == ',' {
            tokens.push(Token::Comma);
        } else if cur == '(' {
            tokens.push(Token::OpenParen);
        } else if cur == ')' {
            tokens.push(Token::CloseParen);
        } else if cur == '{' {
            tokens.push(Token::OpenBrace);
        } else if cur == '}' {
            tokens.push(Token::CloseBrace);
        }
    }

    Ok(tokens)
}

/// parser ///

#[derive(Debug, PartialEq)]
pub enum Expr {
    Num {
        value: u64,
        //val_type: Type,
    },
    Var {
        name: String,
        //var_type: Type,
    },
    BinOp {
        op: char,
        lhs: Box<AstNode>,
        rhs: Box<AstNode>,
    },
    Call {
        name: String,
        args: Vec<AstNode>,
    },
    Proto {
        name: String,
        args: Vec<String>,
    },
    Func {
        proto: Box<AstNode>,
        body: Option<Box<AstNode>>,
    },
}

impl Expr {
    fn format_proto(name: &str, args: &[String]) -> String {
        let mut s = format!("({}", name);
        if !args.is_empty() {
            for arg in args {
                s += &format!(" {}", arg);
            }
        }
        s += ")";
        s
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Num { value } => write!(f, "{}", value),
            Expr::BinOp { op, lhs, rhs } => write!(f, "({} {} {})", op, lhs, rhs),
            Expr::Var { name } => write!(f, "{}", name),
            Expr::Call { name, args } => write!(
                f,
                "{}",
                Expr::format_proto(
                    name,
                    &args.iter().map(|x| x.to_string()).collect::<Vec<_>>()
                )
            ),
            Expr::Proto { name, args } => write!(f, "{}", Expr::format_proto(name, args)),
            Expr::Func { proto, body } => match body {
                Some(body) => write!(f, "(define {} {})", proto, body),
                _ => write!(f, "(define {})", proto),
            },
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct AstNode(Expr);

impl AstNode {
    fn new(value: Expr) -> Self {
        AstNode(value)
    }
}

impl Display for AstNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

enum OpPrec {
    Left(u8),
    Right(u8),
}

impl OpPrec {
    fn prec(op: char) -> Result<OpPrec, String> {
        match op {
            '^' => Ok(OpPrec::Right(3)),
            '*' | '/' => Ok(OpPrec::Left(2)),
            '+' | '-' => Ok(OpPrec::Left(1)),
            x => Err(format!("Unknown operator: {}", x)),
        }
    }
}

type ParseResult = Result<AstNode, String>;

pub struct Parser<'a> {
    ast: Vec<AstNode>,
    tokens: std::iter::Peekable<std::slice::Iter<'a, Token>>,
}

impl<'a> Parser<'a> {
    pub fn new(tokens: &'a [Token]) -> Self {
        Parser {
            ast: vec![],
            tokens: tokens.iter().peekable(),
        }
    }

    pub fn parse(mut self) -> Result<Vec<AstNode>, String> {
        while let Some(t) = self.tokens.peek() {
            let node = match t {
                Token::Fn => self.parse_function()?,
                _ => self.parse_expression(0)?,
            };
            self.ast.push(node);
        }

        Ok(self.ast)
    }

    // Parses arbitrary length binary expressions.
    fn parse_expression(&mut self, min_p: u8) -> ParseResult {
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

    fn parse_function(&mut self) -> ParseResult {
        // Eat 'fn'
        self.tokens.next();

        let proto = self.parse_proto()?;

        match self.tokens.next() {
            Some(t @ Token::OpenBrace) => t,
            Some(_) | None => return Err("Expecting '{' in function definition".to_string()),
        };

        // If close brace, body is empty.
        let body: Option<Box<AstNode>> = match self.tokens.peek() {
            Some(Token::CloseBrace) => None,
            Some(_) => Some(Box::new(self.parse_expression(0)?)),
            None => return Err("Expecting '}' in function definition".to_string()),
        };

        let node = AstNode::new(Expr::Func {
            proto: Box::new(proto),
            body,
        });

        match self.tokens.next() {
            Some(t @ Token::CloseBrace) => t,
            Some(_) | None => return Err("Expecting '}' in function definition".to_string()),
        };

        Ok(node)
    }

    fn parse_proto(&mut self) -> ParseResult {
        let fn_name = match self.tokens.next() {
            Some(Token::Ident(t)) => t,
            Some(_) | None => return Err("Expecting function name".to_string()),
        };

        match self.tokens.next() {
            Some(t @ Token::OpenParen) => t,
            Some(_) | None => return Err("Expecting '(' in prototype)".to_string()),
        };

        let mut args: Vec<String> = vec![];
        while let Some(&next) = self.tokens.peek() {
            if *next == Token::CloseParen {
                break;
            }

            let id = match self.tokens.next() {
                Some(Token::Ident(t)) => t,
                Some(_) | None => return Err("Expecting identifier in prototype)".to_string()),
            };

            args.push(id.to_string());

            let &next = match self.tokens.peek() {
                Some(t) => t,
                None => return Err("Premature end. Expecting ',' or ')'.".to_string()),
            };

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

        Ok(AstNode::new(Expr::Proto {
            name: fn_name.to_string(),
            args,
        }))
    }

    // Returns atomic expression components.
    fn parse_primary(&mut self) -> ParseResult {
        let node = if let Some(t) = self.tokens.next() {
            match t {
                Token::Int(n) => self.parse_num(*n),
                Token::Ident(id) => self.parse_ident(id),
                Token::OpenParen => self.parse_paren(),
                x => return Err(format!("Expecting primary expression. Got: {}", x)),
            }
        } else {
            unreachable!("parse_primary()");
        };
        node
    }

    fn parse_num(&self, n: u64) -> ParseResult {
        Ok(AstNode::new(Expr::Num { value: n }))
    }

    fn parse_ident(&mut self, id: &str) -> ParseResult {
        let node = AstNode::new(Expr::Var {
            name: id.to_owned(),
        });

        // If next is not a '(', the current token is just a simple var.
        match self.tokens.peek() {
            Some(t @ Token::OpenParen) => t,
            Some(_) | None => return Ok(node),
        };

        // Eat open paren
        self.tokens.next();

        let mut args: Vec<AstNode> = vec![];
        while let Some(&next) = self.tokens.peek() {
            if *next == Token::CloseParen {
                break;
            }
            args.push(self.parse_expression(0)?);

            let &next = match self.tokens.peek() {
                Some(t) => t,
                None => return Err("Premature end. Expecting ',' or ')'.".to_string()),
            };

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

        Ok(AstNode::new(Expr::Call {
            name: id.to_owned(),
            args,
        }))
    }

    fn parse_op(&self, op: char, lhs: AstNode, rhs: AstNode) -> ParseResult {
        Ok(AstNode::new(Expr::BinOp {
            op,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }))
    }

    fn parse_paren(&mut self) -> ParseResult {
        let lhs = self.parse_expression(0);
        self.tokens.next(); // Eat ')'
        lhs
    }
}
