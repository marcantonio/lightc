#[macro_export]
macro_rules! numeric_types {
    () => {
        Type::Int32 | Type::Int64 | Type::UInt32 | Type::UInt64 | Type::Float | Type::Double
    };
}

#[macro_export]
macro_rules! int_types {
    () => {
        Type::Int32 | Type::Int64 | Type::UInt32 | Type::UInt64
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
        Type::Int32 | Type::Int64
    };
}

#[macro_export]
macro_rules! unsigned_int_types {
    () => {
        Type::UInt32 | Type::UInt64
    };
}

#[macro_export]
macro_rules! float_types {
    () => {
        Type::Float | Type::Double
    };
}
