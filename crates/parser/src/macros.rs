#[macro_export]
macro_rules! expect_next_token {
    // Matches patterns like TokenType::Let
    ($ts:expr, $( TokenType::$v:tt )|+ , $err:expr) => {
        let t = $ts.next();
        match t {
            $( Some(Token { tt: TokenType::$v, .. }) => (), )+
                _ => {
                    // Default to EOF. Make sure that we ignore inserted
                    // semicolons.
                    let new_t = t.cloned().filter(|n| !n.is_implicit_semi()).unwrap_or_default();
                    return Err(ParseError::from((
                        format!(
                            "{}. Got `{}`",
                            $err.to_string(),
                            new_t.tt
                        ),
                        &new_t
                    )))
                }
        }
    };

    // Matches patterns like TokenType::Op(Operator::Assign)
    ($ts:expr, $( TokenType::$v:tt(Operator::$s:tt) )|+ , $err:expr) => {
        let t = $ts.next();
        match t {
            $( Some(Token { tt: TokenType::$v(Operator::$s), .. }) => (), )+
                _ => {
                    // Default to EOF. Make sure that we ignore inserted
                    // semicolons.
                    let new_t = t.cloned().filter(|n| !n.is_implicit_semi()).unwrap_or_default();
                    return Err(ParseError::from((
                        format!(
                            "{}. Got `{}`",
                            $err.to_string(),
                            new_t.tt
                        ),
                        &new_t
                    )))
                }
        }
    };

    // Matches patterns like TokenType::Ident(_) and used for return value
    ($ts:expr, TokenType::$v:tt($_:tt), $err:expr) => {
        {
            let t = $ts.next();
            match t {
                Some(Token { tt: TokenType::$v(inner), .. }) => inner,
                _ => {
                    // Default to EOF. Make sure that we ignore inserted
                    // semicolons.
                    let new_t = t.cloned().filter(|n| !n.is_implicit_semi()).unwrap_or_default();
                    return Err(ParseError::from((
                        format!(
                            "{}. Got `{}`",
                            $err.to_string(),
                            new_t.tt
                        ),
                        &new_t
                    )))
                }
            }
        }
    };
}

#[macro_export]
macro_rules! expect_explicit_semi {
    ($ts:expr, $err:expr) => {{
        let t = $ts.next();
        match t {
            Some(Token { tt: TokenType::Semicolon(false), .. }) => (),
            _ => {
                let new_t = t.cloned().filter(|n| !n.is_implicit_semi()).unwrap_or_default();
                return Err(ParseError::from((format!("{}. Got `{}`", $err.to_string(), new_t.tt), &new_t)));
            },
        }
    }};
}

// Matches token type and executes $and or returns None
#[macro_export]
macro_rules! token_is_and_then {
    ($to:expr, $tt:pat, $and:expr) => {
        match $to {
            Some(Token { tt: $tt, .. }) => Some($and),
            _ => None,
        }
    };
}
