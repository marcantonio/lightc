use std::{sync::atomic::{AtomicUsize, Ordering}, collections::HashMap};

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

#[derive(Debug)]
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
        lhs: Box<ExprAst>,
        rhs: Box<ExprAst>,
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
    tokens.get(idx)
}

fn peek_token(tokens: &[Token]) -> Option<&Token> {
    let idx = IDX.load(Ordering::Relaxed);
    tokens.get(idx)
}


pub fn parse(tokens: &mut [Token], settings: Settings) -> Vec<ExprAst> {
    let ast: Vec<ExprAst> = vec![];
    loop {
        let res = parse_expression(tokens, &settings);
        if let Some(expr) = res {
            println!("{:?}", expr);
        } else {
            break;
        };
    }

    /*
       while let Some(cur) = tokens.last() {
           ast.push(match cur {
               Token::Int(n) => parse_num(*n),
               Token::Fn => todo!(),
               Token::Let => todo!(),
               Token::OpenParen => todo!(),
               Token::CloseParen => todo!(),
               Token::OpenBrace => todo!(),
               Token::CloseBrace => todo!(),
               Token::Comma => todo!(),
               Token::Colon => todo!(),
               Token::Assign => todo!(),
               Token::Ident(id) => parse_ident(id),
               Token::VarType(_) => todo!(),
               Token::Op(_) => todo!(),
           });
       }

    */
    println!("{:?}", ast);

    ast
}

fn parse_expression(tokens: &[Token], settings: &Settings) -> Option<ExprAst> {
    if let Some(lhs) = parse_primary(tokens) {
        println!(">parse_primary lhs: {:?}", lhs);
        let rhs = parse_binop_rhs(tokens, lhs, 0, settings);
        println!(">parse_primary rhs: {:?}", rhs);
        rhs
    } else {
        None
    }
}

fn parse_binop_rhs(tokens: &[Token], mut lhs: ExprAst, min_prec: i32, settings: &Settings) -> Option<ExprAst> {
    println!("in binop with next: {:?}", tokens[IDX.load(Ordering::Relaxed)]);
    while let Some(next) = peek_token(tokens) {
        if let Some(prec) = settings.get_precedence_for(next) {
            if prec < min_prec {
                // Not high enough precedence
                return Some(lhs);
            }

            // Op found
            println!(">op: {:?}", next);
            let op = next;
            let next = next_token(tokens).unwrap();
            println!(">next: {:?}", next);
            if let Some(rhs) = parse_primary(tokens) {
                println!(">rhs: {:?}", rhs);
                if let Some(next_prec) = settings.get_precedence_for(next) {
                    if prec < next_prec {
                        if let Some(rhs) = parse_binop_rhs(tokens, rhs, prec+1, settings) {
                            if let Token::Op(op) = op {
                                lhs = ExprAst::BinOp { op: *op, lhs: Box::new(lhs), rhs: Box::new(rhs) };
                            }
                        } else {
                            println!("no rhs2");
                            break;
                        }
                    }
                }
            } else {
                println!("no rhs");
                break;
            }
        } else {
            // Return if it's not an operator
            return Some(lhs);
        }
    }
    None
}

fn parse_primary(tokens: &[Token]) -> Option<ExprAst> {
    if let Some(t) = next_token(tokens) {
        match t {
            Token::Int(n) => Some(parse_num(*n)),
            Token::Ident(id) => Some(parse_ident(id)),
            x => {
                println!("Expecting expression token. Got: {}", x);
                None
            }
        }
    } else {
        None
    }
}

fn parse_num(n: u64) -> ExprAst {
    ExprAst::Num { value: n }
}

fn parse_ident(id: &str) -> ExprAst {
    ExprAst::Var {
        name: id.to_owned(),
    }
}
