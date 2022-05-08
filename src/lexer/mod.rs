use serde::Serialize;
use std::iter::Peekable;

use crate::token::{Symbol, Token, TokenType, Type};

type LexResult = std::result::Result<Token, LexError>;

pub(crate) struct Lexer {
    stream: Peekable<StreamIter<char>>,
    pub tokens: Vec<Token>,
}

impl Lexer {
    pub fn new(input: &str) -> Self {
        Lexer {
            stream: StreamIter::new(input).peekable(),
            tokens: vec![],
        }
    }

    // Scan all input
    pub fn scan(mut self) -> Result<Vec<Token>, LexError> {
        loop {
            let token = self.lex()?;
            if token.is_eof() {
                break;
            }
            self.tokens.push(token);
        }
        Ok(self.tokens)
    }

    // Recursively process enough characters to produce one token
    fn lex(&mut self) -> LexResult {
        let cur = match self.stream.next() {
            Some(cur) => cur,
            None => unreachable!("fatal: can't lex nothing"),
        };

        // Inject a semicolon if certain tokens occur at the end of the line or
        // EOF. If EOF, make sure the context is right.
        if cur.value == '\n' && self.should_add_semicolon() {
            return Ok(Token::from((TokenType::Semicolon(true), cur)));
        } else if cur.is_eof() {
            if self.should_add_semicolon() {
                let semi = match self.tokens.last() {
                    Some(t) => Token::new(TokenType::Semicolon(true), t.line, t.column + 1),
                    None => Token::default(),
                };
                self.tokens.push(semi);
            }
            return Ok(Token::from((TokenType::Eof, cur)));
        }

        // Ignore whitespace
        if cur.value.is_ascii_whitespace() {
            while let Some(c) = self.stream.peek() {
                if !c.value.is_ascii_whitespace() {
                    return self.lex();
                } else if c.is_eof() {
                    break;
                }
                self.stream.next();
            }
            return self.lex(); // Eat trailing newline
        }

        // Single line comments
        if cur == '/' && matches!(self.stream.peek(), Some(c) if *c == '/') {
            while let Some(c) = self.stream.next() {
                if c == '\n' {
                    return self.lex();
                } else if c.is_eof() {
                    break;
                }
            }
            return self.lex(); // Eat trailing comment
        }

        // Keywords, types, and identifiers
        if cur.value.is_ascii_alphabetic() {
            let mut identifier = String::from(cur.value);
            while let Some(c) = self.stream.peek() {
                if c.value.is_ascii_alphanumeric() || *c == '_' {
                    identifier.push(c.value);
                    self.stream.next();
                } else {
                    break;
                }
            }

            let tt = match identifier.as_str() {
                "fn" => TokenType::Fn,
                "let" => TokenType::Let,
                "for" => TokenType::For,
                "if" => TokenType::If,
                "else" => TokenType::Else,
                "extern" => TokenType::Extern,
                "true" => TokenType::Bool(true),
                "false" => TokenType::Bool(false),
                "int8" => TokenType::VarType(Type::Int8),
                "int16" => TokenType::VarType(Type::Int16),
                "int32" => TokenType::VarType(Type::Int32),
                "int64" => TokenType::VarType(Type::Int64),
                "uint8" => TokenType::VarType(Type::UInt8),
                "uint16" => TokenType::VarType(Type::UInt16),
                "uint32" => TokenType::VarType(Type::UInt32),
                "uint64" => TokenType::VarType(Type::UInt64),
                "float" => TokenType::VarType(Type::Float),
                "double" => TokenType::VarType(Type::Double),
                "bool" => TokenType::VarType(Type::Bool),
                "char" => TokenType::VarType(Type::Char),
                // TODO: don't hardcode these
                "int" => TokenType::VarType(Type::Int32),
                "uint" => TokenType::VarType(Type::UInt32),
                _ => TokenType::Ident(identifier),
            };

            return Ok(Token::from((tt, cur)));
        }

        // Literal numbers
        if cur.value.is_ascii_digit() {
            let mut n = String::from(cur.value);
            while let Some(c) = self.stream.peek() {
                if c.value.is_ascii_alphanumeric() || *c == '.' {
                    n.push(c.value);
                    self.stream.next();
                } else {
                    break;
                }
            }

            return Ok(Token::from((TokenType::Num(n), cur)));
        }

        // Literal char
        if cur == '\'' {
            let mut ch = String::new();
            let next = self
                .stream
                .next()
                .unwrap_or_else(|| unreachable!("fatal: lexed None when looking for char"));

            match next.value {
                // Control characters
                '\\' => {
                    if let Some(next) = self.stream.next() {
                        match next.value {
                            'n' => ch = String::from("\n"),
                            't' => ch = String::from("\t"),
                            '\'' => ch = String::from("'"),
                            c => {
                                return Err(LexError::from((
                                    format!("Invalid character control sequence: `\\{}`", c),
                                    next,
                                )))
                            }
                        }
                    }
                }
                // EOF
                '\0' => {
                    return Err(LexError::from((
                        "Unterminated character literal. Expecting `'`, got `EOF`".to_string(),
                        cur,
                    )));
                }
                '\'' => {
                    return Err(LexError::from((
                        "Character literal can't be empty".to_string(),
                        cur,
                    )))
                }

                // Everything else
                c => ch = String::from(c),
            }

            // Check for closing '\''
            let last = self
                .stream
                .next()
                .unwrap_or_else(|| unreachable!("fatal: lexed None when looking for `'`"));
            match last.value {
                '\'' => (),
                '\0' | '\n' => {
                    return Err(LexError::from((
                        "Unterminated character literal. Expecting `'`".to_string(),
                        last,
                    )));
                }
                _ => {
                    return Err(LexError::from((
                        format!("Invalid character sequence: `'{}{}'`", ch, last.value),
                        last,
                    )));
                }
            }

            return Ok(Token::from((TokenType::Char(ch), cur)));
        }

        // Multi-character operators
        if let Some(next) = self.stream.peek() {
            match cur.value {
                '=' if next == &'=' => {
                    self.stream.next();
                    return Ok(Token::from((TokenType::Op(Symbol::Eq), cur)));
                }
                '&' if next == &'&' => {
                    self.stream.next();
                    return Ok(Token::from((TokenType::Op(Symbol::And), cur)));
                }
                '|' if next == &'|' => {
                    self.stream.next();
                    return Ok(Token::from((TokenType::Op(Symbol::Or), cur)));
                }
                '-' if next == &'>' => {
                    self.stream.next();
                    return Ok(Token::from((TokenType::Op(Symbol::RetType), cur)));
                }
                _ => (),
            }
        }

        // Everything else
        let tt = match cur.value {
            '+' => TokenType::Op(Symbol::Add),
            '-' => TokenType::Op(Symbol::Sub),
            '*' => TokenType::Op(Symbol::Mul),
            '/' => TokenType::Op(Symbol::Div),
            '^' => TokenType::Op(Symbol::Pow),
            '>' => TokenType::Op(Symbol::Gt),
            '<' => TokenType::Op(Symbol::Lt),
            '!' => TokenType::Op(Symbol::Not),
            '=' => TokenType::Op(Symbol::Assign),
            '}' => TokenType::CloseBrace,
            ')' => TokenType::CloseParen,
            ':' => TokenType::Colon,
            ',' => TokenType::Comma,
            '{' => TokenType::OpenBrace,
            '(' => TokenType::OpenParen,
            ';' => TokenType::Semicolon(false),
            c => {
                return Err(LexError::from((format!("Unknown character: {}", c), cur)));
            }
        };

        Ok(Token::from((tt, cur)))
    }

    // Add a semicolon for these tokens
    fn should_add_semicolon(&self) -> bool {
        use TokenType::*;

        if let Some(t) = self.tokens.last() {
            matches!(
                t.tt,
                Bool(_) | Char(_) | CloseBrace | CloseParen | Ident(_) | Num(_) | VarType(_)
            )
        } else {
            false
        }
    }
}

// Provides additional context for each source character
#[derive(Debug, Clone, Copy, PartialEq)]
struct ContextElement<T> {
    value: T,
    line: usize,
    column: usize,
}

impl<T> ContextElement<T> {
    fn new(value: T, line: usize, column: usize) -> Self {
        ContextElement {
            value,
            line: line + 1,
            column: column + 1,
        }
    }
}

impl ContextElement<char> {
    // Will cause lexing to stop if there's a null byte in the file
    fn is_eof(&self) -> bool {
        self.value == 0 as char
    }
}

impl PartialEq<char> for ContextElement<char> {
    fn eq(&self, other: &char) -> bool {
        self.value == *other
    }
}

impl<T> From<(TokenType, ContextElement<T>)> for Token {
    fn from((ty, ContextElement { line, column, .. }): (TokenType, ContextElement<T>)) -> Self {
        Token {
            tt: ty,
            line,
            column,
        }
    }
}

// Iterator for the source character stream. Supports line and column context.
struct StreamIter<T> {
    lines: Vec<Vec<T>>,
    line: usize,
    column: usize,
}

impl StreamIter<char> {
    fn new(input: &str) -> Self {
        StreamIter {
            lines: input
                .split_inclusive('\n') // can't use .lines() or we lose '\n'
                .map(|l| l.chars().collect())
                .collect(),
            line: 0,
            column: 0,
        }
    }
}

impl Iterator for StreamIter<char> {
    type Item = ContextElement<char>;

    fn next(&mut self) -> Option<Self::Item> {
        let opt = self.lines.get(self.line);
        let line = match opt {
            Some(l) => l,
            None => return Some(ContextElement::new(0 as char, self.line, self.column - 1)),
        };
        let cc = line
            .get(self.column)
            .map(|c| ContextElement::new(*c, self.line, self.column))
            .or_else(|| {
                self.line += 1;
                self.column = 0;
                self.lines.get(self.line).and_then(|line| {
                    line.get(self.column)
                        .map(|c| ContextElement::new(*c, self.line, self.column))
                })
            });
        self.column += 1;
        cc.or_else(|| Some(ContextElement::new(0 as char, self.line, self.column - 1)))
    }
}

#[derive(Debug, PartialEq, Serialize)]
pub(crate) struct LexError {
    message: String,
    line: usize,
    column: usize,
}

impl std::fmt::Display for LexError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Lexing error: {} at {}:{}",
            self.message, self.line, self.column
        )
    }
}

impl std::error::Error for LexError {}

impl<T> From<(String, ContextElement<T>)> for LexError {
    fn from((msg, cp): (String, ContextElement<T>)) -> Self {
        LexError {
            message: msg,
            line: cp.line,
            column: cp.column,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_char() {
        let inputs = vec!["'c'", "'\\n'", "'c", "'mm'", "'", "'\\c'", "''"];
        insta::with_settings!({ snapshot_path => "tests/snapshots", prepend_module_to_snapshot => false }, {
            for input in inputs {
                insta::assert_yaml_snapshot!((input, Lexer::new(input).scan()));
            }
        });
    }

    #[test]
    fn test_cond() {
        insta::with_settings!({ snapshot_path => "tests/snapshots", prepend_module_to_snapshot => false }, {
            let inputs = vec![
"if x > -3 {
    print(x)
}
",
"if x > -3 {
    print(x)
} else {
    exit()
}
",
"if x > 3 {
    print(x)
} else if y == 1 {
    exit()
} else {
    z
}
"];
            for input in inputs {
                insta::assert_yaml_snapshot!((input, Lexer::new(input).scan()));
            }
        });
    }

    #[test]
    fn test_extern() {
        let input = "extern cos(x)";
        insta::with_settings!({ snapshot_path => "tests/snapshots", prepend_module_to_snapshot => false }, {
            insta::assert_yaml_snapshot!((input, Lexer::new(input).scan()));
        });
    }

    #[test]
    fn test_fn() {
        let input = "\
fn foo(a, b, c) -> int {
    bar(a) + 2
}";
        insta::with_settings!({ snapshot_path => "tests/snapshots", prepend_module_to_snapshot => false }, {
            insta::assert_yaml_snapshot!((input, Lexer::new(input).scan()));
        });
    }

    #[test]
    fn test_for() {
        let input = "\
for let x = 1; x < 10; 1 {
    print(x)
}";
        insta::with_settings!({ snapshot_path => "tests/snapshots", prepend_module_to_snapshot => false }, {
            insta::assert_yaml_snapshot!((input, Lexer::new(input).scan()));
        });
    }

    #[test]
    fn test_logical_ops() {
        let inputs = vec!["x && y", "x || y", "x == y"];
        insta::with_settings!({ snapshot_path => "tests/snapshots", prepend_module_to_snapshot => false }, {
            for input in inputs {
                insta::assert_yaml_snapshot!((input, Lexer::new(input).scan()));
            }
        });
    }

    #[test]
    fn test_let() {
        let inputs = vec![
            "let a: int = 1",
            "let b: int32 = 2",
            "let b: int64 = 3",
            "let b: uint = 4",
            "let b: uint32 = 5",
            "let b: uint64 = 6",
            "let c: float = 7.0",
            "let c: double = 8.0",
            "let d: bool = true",
            "let d: bool = false",
            "let e: char = 'c'",
            "let e: char = '\n'",
        ];
        insta::with_settings!({ snapshot_path => "tests/snapshots", prepend_module_to_snapshot => false }, {
            for input in inputs {
                insta::assert_yaml_snapshot!((input, Lexer::new(input).scan()));
            }
        });
    }

    #[test]
    fn test_multi_line_comment() {
        let input = "\
let foo = 14
// line1
// line2
foo
";
        insta::with_settings!({ snapshot_path => "tests/snapshots", prepend_module_to_snapshot => false }, {
            insta::assert_yaml_snapshot!((input, Lexer::new(input).scan()));
        });
    }

    #[test]
    fn test_ops() {
        let input = "(x + y) * 4 / 4";
        insta::with_settings!({ snapshot_path => "tests/snapshots", prepend_module_to_snapshot => false }, {
            insta::assert_yaml_snapshot!((input, Lexer::new(input).scan()));
        });
    }

    #[test]
    fn test_semi() {
        let inputs = vec!["a", "1", "a()", "{ a }", "let a: int", "let", "fn", "'c'"];
        insta::with_settings!({ snapshot_path => "tests/snapshots", prepend_module_to_snapshot => false }, {
            for input in inputs {
                insta::assert_yaml_snapshot!((input, Lexer::new(input).scan()));
            }
        });
    }

    #[test]
    fn test_trailing_comment() {
        let input = "\
let foo = 13
// line2";
        insta::with_settings!({ snapshot_path => "tests/snapshots", prepend_module_to_snapshot => false }, {
            insta::assert_yaml_snapshot!((input, Lexer::new(input).scan()));
        });
    }

    #[test]
    fn test_unknown_char() {
        let input = "let foo = `1`";
        insta::with_settings!({ snapshot_path => "tests/snapshots", prepend_module_to_snapshot => false }, {
            insta::assert_yaml_snapshot!((input, Lexer::new(input).scan()));
        });
    }

    #[test]
    fn test_lex_one() {
        use Symbol::*;
        use TokenType::*;

        let input = "\
foo + bar
// bar
/ not_a_comment
baz
";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.lex(), Ok(Token::new(Ident("foo".to_string()), 1, 1)));
        assert_eq!(lexer.lex(), Ok(Token::new(Op(Add), 1, 5)));
        assert_eq!(lexer.lex(), Ok(Token::new(Ident("bar".to_string()), 1, 7)));
        assert_eq!(lexer.lex(), Ok(Token::new(Op(Div), 3, 1)));
        assert_eq!(
            lexer.lex(),
            Ok(Token::new(Ident("not_a_comment".to_string()), 3, 3))
        );
        assert_eq!(lexer.lex(), Ok(Token::new(Ident("baz".to_string()), 4, 1)));
        assert_eq!(lexer.lex(), Ok(Token::new(Eof, 5, 1)));
    }

    #[test]
    fn test_stream_next() {
        let input = "\
abc
def
ghi
";
        let mut stream = StreamIter::new(input);
        assert_eq!(ContextElement::new('a', 0, 0), stream.next().unwrap());
        assert_eq!(ContextElement::new('b', 0, 1), stream.next().unwrap());
        assert_eq!(ContextElement::new('c', 0, 2), stream.next().unwrap());
        assert_eq!(ContextElement::new('\n', 0, 3), stream.next().unwrap());
        assert_eq!(ContextElement::new('d', 1, 0), stream.next().unwrap());
        assert_eq!(ContextElement::new('e', 1, 1), stream.next().unwrap());
        assert_eq!(ContextElement::new('f', 1, 2), stream.next().unwrap());
        assert_eq!(ContextElement::new('\n', 1, 3), stream.next().unwrap());
        assert_eq!(ContextElement::new('g', 2, 0), stream.next().unwrap());
        assert_eq!(ContextElement::new('h', 2, 1), stream.next().unwrap());
        assert_eq!(ContextElement::new('i', 2, 2), stream.next().unwrap());
        assert_eq!(ContextElement::new('\n', 2, 3), stream.next().unwrap());
        assert_eq!(ContextElement::new(0 as char, 3, 0), stream.next().unwrap());
        assert_eq!(ContextElement::new(0 as char, 3, 0), stream.next().unwrap());
    }
}
