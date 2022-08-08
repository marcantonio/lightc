use serde::Serialize;
use std::fmt::Display;

use common::{Symbol, ToSymbol, Type};

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

impl ToSymbol for Prototype {
    fn to_symbol(&self) -> Symbol {
        Symbol::new_fn(
            self.name(),
            // XXX: ignore these for now. Maybe this should just be types and not symbols,
            // i.e., a signature?
            self.args().iter().map(|(name, ty)| (name.as_ref(), ty).to_symbol()).collect::<Vec<Symbol>>(),
            self.ret_ty().unwrap_or_default(),
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
