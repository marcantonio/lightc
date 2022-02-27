use crate::token::Symbol;

pub(crate) enum OpPrec {
    Left(u8),
    Right(u8),
}

// Precedence tables for binary and unary operators
impl OpPrec {
    pub(crate) fn bin_prec(op: Symbol) -> Result<OpPrec, String> {
        use Symbol::*;
        match op {
            Pow => Ok(OpPrec::Right(8)),
            Mult | Div => Ok(OpPrec::Left(7)),
            Plus | Minus => Ok(OpPrec::Left(6)),
            Gt | Lt => Ok(OpPrec::Left(5)),
            Eq => Ok(OpPrec::Left(4)),
            And => Ok(OpPrec::Left(3)),
            Assign => Ok(OpPrec::Left(2)),
            Or => Ok(OpPrec::Left(1)),
            x => Err(format!("Unknown binary operator: {}", x)),
        }
    }

    pub(crate) fn un_prec(op: Symbol) -> Result<u8, String> {
        use Symbol::*;
        match op {
            Not => Ok(9),
            Minus => Ok(8),
            x => Err(format!("Unknown unary operator: {}", x)),
        }
    }
}
