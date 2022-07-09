use serde::Serialize;
use std::fmt::Display;

use common::symbol_table::SymbolId;
use common::{Symbol, Type};

#[derive(Debug, PartialEq, Clone, Serialize)]
pub struct Prototype {
    name: String,
    args: Vec<(String, Type)>,
    ret_ty: Option<Type>,
}

impl Prototype {
    pub fn new(name: String, args: Vec<(String, Type)>, ret_ty: Option<Type>) -> Prototype {
        Prototype { name, args, ret_ty }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn set_name(&mut self, name: String) {
        self.name = name;
    }

    pub fn args(&self) -> &[(String, Type)] {
        &self.args
    }

    pub fn set_args(&mut self, args: Vec<(String, Type)>) {
        self.args = args;
    }

    pub fn ret_ty(&self) -> Option<&Type> {
        self.ret_ty.as_ref()
    }

    pub fn set_ret_ty(&mut self, ret_ty: Option<&Type>) {
        self.ret_ty = ret_ty.map(Type::to_owned);
    }
}

impl SymbolId for Prototype {
    fn as_symbol_id(&self) -> String {
        let args = self.args().iter().fold(String::new(), |mut acc, (name, ty)| {
            acc += format!("{}:{}~", name, ty).as_str();
            acc
        });
        let ret_ty = format!("{}", self.ret_ty.as_ref().unwrap_or(&Type::Void)).to_ascii_lowercase();

        format!("{}~{}{}", self.name(), args, ret_ty)
    }
}

impl From<&Prototype> for Symbol {
    fn from(proto: &Prototype) -> Self {
        Symbol::new_fn(
            proto.name(),
            proto.args().iter().map(|(name, ty)| Symbol::from((name.as_ref(), ty))).collect::<Vec<Symbol>>(),
            proto.ret_ty().unwrap_or_default(),
        )
    }
}

impl Display for Prototype {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = format!("({}", self.name);
        if !self.args.is_empty() {
            for arg in &self.args {
                s += &format!(" {}:{}", arg.0, arg.1);
            }
        }
        write!(f, "{})", s)
    }
}

#[cfg(test)]
mod test {
    use crate::Prototype;
    use common::{symbol_table::SymbolId, Type};

    #[test]
    fn test_prototype() {
        use Type::*;

        let tests = [
            (
                Prototype {
                    name: String::from("foo"),
                    args: vec![(String::from("bar"), Int32)],
                    ret_ty: Some(Float),
                },
                "foo~bar:int32~float",
            ),
            (
                Prototype {
                    name: String::from("foo"),
                    args: vec![(String::from("bar"), Int32), (String::from("baz"), Int32)],
                    ret_ty: Some(Float),
                },
                "foo~bar:int32~baz:int32~float",
            ),
            (
                Prototype {
                    name: String::from("foo"),
                    args: vec![(String::from("bar"), Int32), (String::from("baz"), Int32)],
                    ret_ty: None,
                },
                "foo~bar:int32~baz:int32~void",
            ),
            (Prototype { name: String::from("foo"), args: vec![], ret_ty: Some(Float) }, "foo~float"),
        ];

        for test in tests {
            assert_eq!(test.0.as_symbol_id(), test.1)
        }
    }
}
