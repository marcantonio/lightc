// Try to convert `$v` to `$ty`. Store result wrapped in `Literal::$variant` and
// assign to `$lit`. Return `Type::$variant`.
#[macro_export]
macro_rules! convert_num {
    ($lit:expr, $val:expr, $variant:ident, $ty:ty) => {{
        let v = <$ty>::try_from(*$val).map_err(|_| "Numeric literal out of range")?;
        *$lit = Literal::$variant(v);
        Type::$variant
    }};
}
