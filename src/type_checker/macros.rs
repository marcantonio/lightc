#[macro_export]
macro_rules! numeric_types {
    () => {
        int_types!() | float_types!()
    };
}

#[macro_export]
macro_rules! int_types {
    () => {
        signed_int_types!() | unsigned_int_types!()
    };
}

#[macro_export]
macro_rules! int8_types {
    () => {
        Type::Int8 | Type::UInt8
    };
}

#[macro_export]
macro_rules! int16_types {
    () => {
        Type::Int16 | Type::UInt16
    };
}

#[macro_export]
macro_rules! int32_types {
    () => {
        Type::Int32 | Type::UInt32
    };
}

#[macro_export]
macro_rules! int64_types {
    () => {
        Type::Int64 | Type::UInt64
    };
}

#[macro_export]
macro_rules! signed_int_types {
    () => {
        Type::Int8 | Type::Int16 | Type::Int32 | Type::Int64
    };
}

#[macro_export]
macro_rules! unsigned_int_types {
    () => {
        Type::UInt8 | Type::UInt16 | Type::UInt32 | Type::UInt64
    };
}

#[macro_export]
macro_rules! float_types {
    () => {
        Type::Float | Type::Double
    };
}

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
