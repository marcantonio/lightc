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
        if cur == '+' || cur == '-' || cur == '*' || cur == '/' {
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

/*
pub struct Settings {
    op_precedence: HashMap<char, i32>,
}

impl Settings {
    pub fn new() -> Settings {
        let mut op_precedence = HashMap::new();
        op_precedence.insert('<', 10);
        op_precedence.insert('-', 20);
        op_precedence.insert('+', 30);
        op_precedence.insert('/', 40);
        op_precedence.insert('*', 50);

        Settings { op_precedence }
    }

    fn get_precedence_for(&self, token: &Token) -> Option<i32> {
        if let Token::Op(op) = token {
            self.op_precedence.get(op).copied()
        } else {
            None
        }
    }
}

impl Default for Settings {
    fn default() -> Self {
        Self::new()
    }
}


static IDX: AtomicUsize = AtomicUsize::new(0);

//struct Tokens

fn next_token(tokens: &[Token]) -> Option<&Token> {
    let idx = IDX.fetch_add(1, Ordering::Relaxed);
    tokens.get(idx+1)
}

fn current_token(tokens: &[Token]) -> Option<&Token> {
    let idx = IDX.load(Ordering::Relaxed);
    tokens.get(idx)
}


pub fn parse(tokens: &mut [Token], settings: Settings) -> Vec<ExprAst> {
    let ast: Vec<ExprAst> = vec![];
    loop {
        let res = parse_expression(tokens, &settings);
        if let Some(expr) = res {
            println!("end: {:?}", expr);
        } else {
            break;
        };
    }

//    println!("{:?}", ast);

    ast
}


fn parse_expression(tokens: &[Token], settings: &Settings) -> Option<ExprAst> {
    if let Some(lhs) = parse_primary(tokens) {
        parse_binop_rhs(tokens, lhs, 0, settings)
    } else {
        None
    }
}

fn parse_binop_rhs(tokens: &[Token], mut lhs: ExprAst, min_prec: i32, settings: &Settings) -> Option<ExprAst> {
    println!("in binop with lhs: {:?}, cur: {:?}", lhs, current_token(tokens));

    let mut cur = match current_token(tokens) {
        Some(cur) => cur,
        None => return None,
    };
    loop {
        let prec = match settings.get_precedence_for(cur) {
            Some(p) => p,
            None => {
                println!("returning lhs");
                return Some(lhs)
            },
        };

        if prec < min_prec {
            // Not high enough precedence
            println!("returning lhs2");
            return Some(lhs);
        }

        // Op found
        println!(">op: {:?}", cur);
        let op = cur;
        cur = match next_token(tokens) {
            Some(t) => t,
            None => {
                println!("no next token");
                break;
            }
        };
        println!(">new cur: {:?}", cur);

        let mut rhs = match parse_primary(tokens) {
            Some(rhs) => rhs,
            None => {
                println!("no rhs");
                break;
            }
        };

        println!(">rhs: {:?}", rhs);

        println!(">cur:::{:?}", cur); //out of date
        println!(">current:::{:?}", current_token(tokens));

        cur = match current_token(tokens) {
            Some(t) => t,
            None => {
                println!("no next token2");
                break;
            }
        };

        let next_prec = match settings.get_precedence_for(cur) {
            Some(p) => p,
            None => {
                println!("returning lhs");
                return Some(lhs)
            },
        };

        if prec < next_prec {
            rhs = match parse_binop_rhs(tokens, rhs, prec+1, settings) {
                Some(rhs) => rhs,
                None => {
                    println!("no rhs2");
                    break;
                }
            };

            if let Token::Op(op) = op {
                println!(">>>>>>assigning");
                lhs = ExprAst::BinOp { op: *op, lhs: Box::new(lhs), rhs: Box::new(rhs) };

            }
        }
    }
    None
}

fn parse_primary(tokens: &[Token]) -> Option<ExprAst> {
    if let Some(t) = current_token(tokens) {
        println!(">parse_primary: {:?}", t);
        match t {
            Token::Int(n) => Some(parse_num(tokens, *n)),
            Token::Ident(id) => Some(parse_ident(tokens, id)),
            x => {
                println!("Expecting expression token. Got: {}", x);
                None
            }
        }
    } else {
        None
    }
}

fn parse_num(tokens: &[Token], n: u64) -> ExprAst {
    next_token(tokens);
    ExprAst::Num { value: n }
}

fn parse_ident(tokens: &[Token], id: &str) -> ExprAst {
    next_token(tokens);
    ExprAst::Var {
        name: id.to_owned(),
    }
}
*/

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
            let node = self.parse_expression()?;
            if let Some(node) = node {
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

    fn parse_expression(&mut self) -> Result<Option<AstNode>, String> {
        let node = if let Some(lhs) = self.parse_primary()? {
            if let Some(rhs) = self.binop_rhs(lhs.clone())? {
                Some(rhs)
            } else {
                Some(lhs)
            }
        } else {
            None
        };
        Ok(node)
    }

    fn parse_primary(&mut self) -> Result<Option<AstNode>, String> {
        let node = if let Some(t) = self.tokens.next() {
            let expr = match t {
                Token::Int(n) => self.parse_num(*n),
                Token::Ident(id) => self.parse_ident(id),
                x => {
                    return Err(format!("Expecting expression token. Got: {}", x));
                }
            };
            Some(AstNode::new(expr, None, None))
        } else {
            None
        };
        Ok(node)
    }

    fn binop_rhs(&mut self, lhs: AstNode) -> Result<Option<AstNode>, String> {
        let op = match self.tokens.next() {
            Some(next) => {
                if let Token::Op(op) = next {
                    op
                } else {
                    unimplemented!("no op???")
                }
            }
            None => return Ok(None),
        };

        if let Some(rhs) = self.parse_expression()? {
            Ok(Some(AstNode::new(
                self.parse_op(*op),
                Some(Box::new(lhs)),
                Some(Box::new(rhs)),
            )))
        } else {
            Ok(None)
        }
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
