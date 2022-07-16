use common::Operator;

pub(crate) enum OpPrec {
    Left(u8),
    Right(u8),
}

// Precedence tables for binary and unary operators
impl OpPrec {
    pub(crate) fn bin_prec(op: Operator) -> Result<OpPrec, String> {
        use Operator::*;
        match op {
            Pow => Ok(OpPrec::Right(12)),
            Mul | Div => Ok(OpPrec::Left(10)),
            Add | Sub => Ok(OpPrec::Left(9)),
            Gt | GtEq | Lt | LtEq => Ok(OpPrec::Left(8)),
            Eq | NotEq => Ok(OpPrec::Left(7)),
            BitAnd => Ok(OpPrec::Left(6)),
            BitXor => Ok(OpPrec::Left(5)),
            BitOr => Ok(OpPrec::Left(4)),
            And => Ok(OpPrec::Left(3)),
            Or => Ok(OpPrec::Left(2)),
            Assign | AddEq | SubEq | MulEq | DivEq => Ok(OpPrec::Right(1)),
            x => Err(format!("Unknown binary operator: `{}`", x)),
        }
    }

    pub(crate) fn un_prec(op: Operator) -> Result<u8, String> {
        use Operator::*;
        match op {
            Not => Ok(11),
            Sub => Ok(11),
            x => Err(format!("Unknown unary operator: `{}`", x)),
        }
    }
}
