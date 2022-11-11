#[macro_export]
macro_rules! init_literal {
    ($ty:tt, $val:expr) => {
        hir::Node::new_lit(Literal::$ty($val), Some(Type::$ty))
    };
}
