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
    Int(f64),
    VarType(Type),
    Op(char),
    GreaterThan,
    LessThan,
    Extern,
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Debug, PartialEq)]
pub enum Type {
    F64,
}

#[derive(Debug, PartialEq)]
pub enum LexError {
    InvalidNum,
}

pub type LexResult = std::result::Result<Vec<Token>, LexError>;

pub struct Lexer {}

impl Lexer {
    pub fn lex(&self, input: &str) -> LexResult {
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
                    "f64" => Token::VarType(Type::F64),
                    "extern" => Token::Extern,
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
            if cur == '+'
                || cur == '-'
                || cur == '*'
                || cur == '/'
                || cur == '^'
                || cur == '>'
                || cur == '<'
            {
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
}
