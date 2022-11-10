use serde::Serialize;
use std::fmt::Display;

use crate::Type;

#[derive(Debug, PartialEq, Clone, Serialize)]
pub enum Literal<T> {
    Int8(i8),
    Int16(i16),
    Int32(i32),
    Int64(i64),
    UInt8(u8),
    UInt16(u16),
    UInt32(u32),
    UInt64(u64),
    Float(f32),
    Double(f64),
    Bool(bool),
    Char(u8),
    Array { elements: Vec<T>, inner_ty: Option<Type> },
    Comp(Vec<T>),
}

impl<T: Display> Display for Literal<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Literal::*;

        match self {
            Int8(v) => write!(f, "{}", v),
            Int16(v) => write!(f, "{}", v),
            Int32(v) => write!(f, "{}", v),
            Int64(v) => write!(f, "{}", v),
            UInt8(v) => write!(f, "{}", v),
            UInt16(v) => write!(f, "{}", v),
            UInt32(v) => write!(f, "{}", v),
            UInt64(v) => write!(f, "{}", v),
            Float(v) => write!(f, "{}", v),
            Double(v) => write!(f, "{}", v),
            Bool(v) => write!(f, "{}", v),
            Char(v) => write!(f, "{}", *v as char),
            Array { elements: el, .. } => {
                let mut s = String::from("[");
                if !el.is_empty() {
                    for e in el {
                        s += &format!(" {}", e);
                    }
                }
                write!(f, "{}]", s)
            },
            Comp(_) => todo!(),
        }
    }
}
