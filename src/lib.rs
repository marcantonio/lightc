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

#[derive(Debug, PartialEq, Clone)]
pub enum ExprAst {
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
    },
    Call {
        name: String,
        args: Vec<ExprAst>,
    },
    Proto {
        name: String,
        args: Vec<String>,
    },
    Func {
        proto: Box<ExprAst>,
        body: Vec<ExprAst>,
    },
}

#[derive(Debug, PartialEq, Clone)]
pub struct AstNode {
    value: ExprAst,
    lhs: Option<Box<AstNode>>,
    rhs: Option<Box<AstNode>>,
}

impl AstNode {
    fn new(value: ExprAst, lhs: Option<Box<AstNode>>, rhs: Option<Box<AstNode>>) -> Self {
        AstNode { value, lhs, rhs }
    }
}

enum OpPrec {
    Left(u8),
    Right(u8),
}

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
        loop {
            if self.tokens.peek().is_some() {
                let node = self.parse_expression(0)?;
                self.ast.push(node);
            } else {
                break;
            }
        }

        for node in &self.ast {
            println!("ast:\n{:?}", node);
        }

        Ok(self.ast)
    }

    fn op_prec(op: char) -> Result<OpPrec, String> {
        match op {
            '^' => Ok(OpPrec::Right(3)),
            '*' | '/' => Ok(OpPrec::Left(2)),
            '+' | '-' => Ok(OpPrec::Left(1)),
            x => Err(format!("Unknown operator: {}", x)),
        }
    }

    fn parse_expression(&mut self, min_p: u8) -> Result<AstNode, String> {
        let mut lhs = self.parse_primary()?;

        while let Some(next) = self.tokens.peek() {
            let op = match next {
                Token::Op(op) => op,
                _ => break,
            };

            let p = match Parser::op_prec(*op)? {
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

            self.tokens.next();

            let rhs = self.parse_expression(p)?;
            lhs = AstNode::new(
                self.parse_op(*op),
                Some(Box::new(lhs)),
                Some(Box::new(rhs)),
            );
        }
        Ok(lhs)
    }

    fn parse_primary(&mut self) -> Result<AstNode, String> {
        let node = if let Some(t) = self.tokens.next() {
            let expr = match t {
                Token::Int(n) => self.parse_num(*n),
                Token::Ident(id) => self.parse_ident(id),
                x => {
                    return Err(format!("Expecting expression token. Got: {}", x));
                }
            };
            AstNode::new(expr, None, None)
        } else {
            unimplemented!("oops")
        };
        Ok(node)
    }

    fn parse_num(&self, n: u64) -> ExprAst {
        ExprAst::Num { value: n }
    }

    fn parse_ident(&self, id: &str) -> ExprAst {
        ExprAst::Var {
            name: id.to_owned(),
        }
    }

    fn parse_op(&self, op: char) -> ExprAst {
        ExprAst::BinOp { op }
    }
}

#[test]
fn test_parser_single_num() {
    let input = "19";
    let tokens = lexer(input).unwrap();
    let parser = Parser::new(&tokens);
    let ast = [AstNode::new(ExprAst::Num { value: 19 }, None, None)];
    assert_eq!(parser.parse().unwrap(), ast)
}

#[test]
fn test_parser_two_num_expr() {
    let input = "19 + 21";
    let tokens = lexer(input).unwrap();
    let parser = Parser::new(&tokens);
    let ast = [AstNode {
        value: ExprAst::BinOp { op: '+' },
        lhs: Some(Box::new(AstNode {
            value: ExprAst::Num { value: 19 },
            lhs: None,
            rhs: None,
        })),
        rhs: Some(Box::new(AstNode {
            value: ExprAst::Num { value: 21 },
            lhs: None,
            rhs: None,
        })),
    }];
    assert_eq!(parser.parse().unwrap(), ast)
}

#[test]
fn test_parser_three_num_expr() {
    let input = "19 + 21 + 40";
    let tokens = lexer(input).unwrap();
    let parser = Parser::new(&tokens);
    let ast = [AstNode {
        value: ExprAst::BinOp { op: '+' },
        lhs: Some(Box::new(AstNode {
            value: ExprAst::Num { value: 19 },
            lhs: None,
            rhs: None,
        })),
        rhs: Some(Box::new(AstNode {
            value: ExprAst::BinOp { op: '+' },
            lhs: Some(Box::new(AstNode {
                value: ExprAst::Num { value: 21 },
                lhs: None,
                rhs: None,
            })),
            rhs: Some(Box::new(AstNode {
                value: ExprAst::Num { value: 40 },
                lhs: None,
                rhs: None,
            })),
        })),
    }];
    assert_eq!(parser.parse().unwrap(), ast)
}
