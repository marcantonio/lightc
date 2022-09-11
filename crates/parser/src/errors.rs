use serde::Serialize;

use lexer::token::Token;

#[derive(Debug, PartialEq, Serialize)]
pub struct ParseError {
    message: String,
    line: usize,
    column: usize,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut msg = self.message.to_owned();

        if self.line != 0 && self.column != 0 {
            msg += &format!(" at {}:{}", self.line, self.column);
        }
        write!(f, "{}", msg)
    }
}

impl std::error::Error for ParseError {}

impl From<(String, Token)> for ParseError {
    fn from((msg, t): (String, Token)) -> Self {
        ParseError { message: msg, line: t.line, column: t.column }
    }
}

impl From<(String, &Token)> for ParseError {
    fn from((msg, t): (String, &Token)) -> Self {
        ParseError { message: msg, line: t.line, column: t.column }
    }
}

impl From<String> for ParseError {
    fn from(msg: String) -> Self {
        ParseError { message: msg, line: 0, column: 0 }
    }
}
