use common::Symbol;

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
            Mul | Div => Ok(OpPrec::Left(6)),
            Add | Sub => Ok(OpPrec::Left(5)),
            Gt | Lt => Ok(OpPrec::Left(4)),
            Eq => Ok(OpPrec::Left(4)),
            And => Ok(OpPrec::Left(3)),
            Or => Ok(OpPrec::Left(2)),
            Assign => Ok(OpPrec::Right(1)), // XXX: right
            x => Err(format!("Unknown binary operator: {}", x)),
        }
    }

    pub(crate) fn un_prec(op: Symbol) -> Result<u8, String> {
        use Symbol::*;
        match op {
            Not => Ok(7),
            Sub => Ok(7),
            x => Err(format!("Unknown unary operator: {}", x)),
        }
    }
}