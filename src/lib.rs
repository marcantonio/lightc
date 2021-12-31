use std::fmt::Display;

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

impl Display for ExprAst {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExprAst::Num { value } => write!(f, "{}", value),
            ExprAst::BinOp { op } => write!(f, "{}", op),
            _ => todo!(),
        }
    }
}

#[derive(Debug, PartialEq)]
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

impl Display for AstNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s: String;
        s = match &self.value {
            ExprAst::BinOp { op: value } => format!("({}", value),
            _ => format!("{}", self.value),
        };

        if let Some(lhs) = &self.lhs {
            s += &format!(" {}", lhs);
        }

        if let Some(rhs) = &self.rhs {
            s += &format!(" {})", rhs);
        }

        write!(f, "{}", s)
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

    // Parses arbitrary length binary expressions.
    fn parse_expression(&mut self, min_p: u8) -> Result<AstNode, String> {
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
            let p = match Parser::op_prec(*op)? {
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
            lhs = self.parse_op(*op, lhs, rhs);
        }
        Ok(lhs)
    }

    // Returns atomic expression components.
    fn parse_primary(&mut self) -> Result<AstNode, String> {
        let node = if let Some(t) = self.tokens.next() {
            match t {
                Token::Int(n) => self.parse_num(*n),
                Token::Ident(id) => self.parse_ident(id),
                Token::OpenParen => self.parse_paren(),
                x => {
                    return Err(format!("Expecting primary expression. Got: {}", x));
                }
            }
        } else {
            unimplemented!("oops")
        };
        Ok(node)
    }

    fn parse_num(&self, n: u64) -> AstNode {
        AstNode::new(ExprAst::Num { value: n }, None, None)
    }

    fn parse_ident(&self, id: &str) -> AstNode {
        AstNode::new(
            ExprAst::Var {
                name: id.to_owned(),
            },
            None,
            None,
        )
    }

    fn parse_op(&self, op: char, lhs: AstNode, rhs: AstNode) -> AstNode {
        AstNode::new(ExprAst::BinOp { op }, Some(Box::new(lhs)), Some(Box::new(rhs)))
    }

    fn parse_paren(&self) -> AstNode {
        todo!()
    }
}

#[allow(dead_code)] // this is not dead code...
fn ast_to_string(ast: &[AstNode]) -> String {
    if ast.len() == 1 {
        return ast[0].to_string();
    }

    let mut s = String::new();
    for node in ast {
        s = s + &node.to_string() + "\n";
    }
    s
}

#[test]
fn test_parser_single_num() {
    let input = "19";
    let tokens = lexer(input).unwrap();
    let parser = Parser::new(&tokens);
    let ast = "19";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);
}

#[test]
fn test_parser_two_num_expr() {
    let input = "19 + 21";
    let tokens = lexer(input).unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(+ 19 21)";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);
}

#[test]
fn test_parser_three_num_expr() {
    let input = "19 + 21 + 40";
    let tokens = lexer(input).unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(+ (+ 19 21) 40)";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);
}

#[test]
fn test_parser_precedence_expr() {
    let input = "19 + 21 * 40";
    let tokens = lexer(input).unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(+ 19 (* 21 40))";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);

    let input = "19 * 21 - 40";
    let tokens = lexer(input).unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(- (* 19 21) 40)";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);

    let input = "19 - 21 + 40";
    let tokens = lexer(input).unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(+ (- 19 21) 40)";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);

    let input = "19 - 21 * 20 + 40";
    let tokens = lexer(input).unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(+ (- 19 (* 21 20)) 40)";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);
}

#[test]
fn test_parser_right_assoc_expr() {
    let input = "19 ^ 21 ^ 40";
    let tokens = lexer(input).unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(^ 19 (^ 21 40))";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);

    let input = "19 ^ 21 + 40";
    let tokens = lexer(input).unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(+ (^ 19 21) 40)";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);

    let input = "19 ^ 21 ^ 40 / 2";
    let tokens = lexer(input).unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(/ (^ 19 (^ 21 40)) 2)";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);
}

#[test]
fn test_parser_multiple_exprs() {
    let input = "19 ^ 21 ^ 40 19 - 21 * 20 + 40";
    let tokens = lexer(input).unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(^ 19 (^ 21 40))\n(+ (- 19 (* 21 20)) 40)\n";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);
}

#[test]
fn test_parser_paren_precedence_expr() {
    let input = "(19 + 21) / 40";
    let tokens = lexer(input).unwrap();
    let parser = Parser::new(&tokens);
    let ast = "(/ (+ 19 21) 40)";
    assert_eq!(ast_to_string(&parser.parse().unwrap()), ast);
}
