// Try to convert `$v` to `$ty`. Store result wrapped in `Literal::$variant` and
// assign to `$lit`. Return `Type::$variant`.
#[macro_export]
macro_rules! convert_num {
    ($val:expr, $variant:ident, $ty:ty) => {{
        let v = <$ty>::try_from($val).map_err(|_| "Numeric literal out of range")?;
        (Literal::$variant(v), Type::$variant)
    }};
}

#[macro_export]
macro_rules! init_literal {
    (Array, $ty:expr, $len:expr) => {
        ast::Node::new_lit(
            Literal::Array { elements: Vec::with_capacity($len), inner_ty: Some(*$ty.clone()) },
            Some(Type::Array(Box::new(*$ty.clone()), $len)),
        )
    };

    ($ty:tt, $val:expr) => {
        ast::Node::new_lit(Literal::$ty($val), Some(Type::$ty))
    };
}
