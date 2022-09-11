use crate::Symbolic;
use common::Type;

#[derive(Clone, PartialEq, Debug)]
pub struct FnData {
    args: Vec<(String, Type)>,
    ret_ty: Type,
    is_extern: bool,
}

#[derive(Clone, PartialEq, Debug)]
pub struct VarData {
    pub ty: Type,
}

#[derive(Clone, PartialEq, Debug)]
pub struct StructData {
    pub fields: Vec<(String, Type)>,
    pub methods: Option<Vec<String>>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Symbol {
    pub name: String,
    pub data: AssocData,
}

#[derive(Clone, PartialEq, Debug)]
pub enum AssocData {
    Fn(FnData),
    Var(VarData),
    Struct(StructData),
    Type(),
}

impl Symbol {
    pub fn new_ty(name: &str) -> Self {
        Symbol { name: String::from("_type_") + name, data: AssocData::Type() }
    }

    pub fn set_name(&mut self, name: &str) {
        self.name = name.to_owned();
    }

    pub fn ty(&self) -> &Type {
        match &self.data {
            AssocData::Var(s) => &s.ty,
            _ => unreachable!("expected symbol to be a variable"),
        }
    }

    pub fn args(&self) -> Vec<(&str, &Type)> {
        match &self.data {
            AssocData::Fn(s) => s.args.iter().map(|(a, ty)| (a.as_str(), ty)).collect(),
            _ => unreachable!("expected symbol to be a function"),
        }
    }

    pub fn arg_tys(&self) -> Vec<&Type> {
        match &self.data {
            AssocData::Fn(s) => s.args.iter().map(|(_, ty)| ty).collect(),
            _ => unreachable!("expected symbol to be a function"),
        }
    }

    pub fn ret_ty(&self) -> &Type {
        match &self.data {
            AssocData::Fn(s) => &s.ret_ty,
            _ => unreachable!("expected symbol to be a function"),
        }
    }

    pub fn is_extern(&self) -> bool {
        match &self.data {
            AssocData::Fn(s) => s.is_extern,
            _ => unreachable!("expected symbol to be a function"),
        }
    }
}

impl Symbolic for Symbol {
    fn name(&self) -> &str {
        &self.name
    }
}

// For new functions
impl From<(&str, &[(String, Type)], &Type, bool)> for Symbol {
    fn from((name, args, ret_ty, is_extern): (&str, &[(String, Type)], &Type, bool)) -> Self {
        Symbol {
            name: name.to_owned(),
            data: AssocData::Fn(FnData { args: args.to_owned(), ret_ty: ret_ty.to_owned(), is_extern }),
        }
    }
}

// For new variables
impl From<(&str, &Type)> for Symbol {
    fn from((name, ty): (&str, &Type)) -> Self {
        Symbol { name: name.to_owned(), data: AssocData::Var(VarData { ty: ty.to_owned() }) }
    }
}

impl From<&(String, Type)> for Symbol {
    fn from((name, ty): &(String, Type)) -> Self {
        Symbol { name: name.to_owned(), data: AssocData::Var(VarData { ty: ty.to_owned() }) }
    }
}
