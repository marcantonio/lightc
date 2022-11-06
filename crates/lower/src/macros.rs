#[macro_export]
macro_rules! init_literal {
    (Array, $ty:expr, $len:expr) => {
        hir::Node::new_lit(
            Literal::Array { elements: Vec::with_capacity($len), inner_ty: Some(*$ty.clone()) },
            Some(Type::Array(Box::new(*$ty.clone()), $len)),
        )
    };

    ($ty:tt, $val:expr) => {
        hir::Node::new_lit(Literal::$ty($val), Some(Type::$ty))
    };
}
