#[macro_export]
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
#[macro_export]
macro_rules! token_is_and_then {
    ($to:expr, $tt:pat, $and:expr) => {
        match $to {
            Some(Token { tt: $tt, .. }) => Some($and),
            _ => None,
        }
    };
}
