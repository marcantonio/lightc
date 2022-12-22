use super::Symbolic;
use crate::Type;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct FnData {
    args: Vec<(String, Type)>,
    ret_ty: Type,
    is_extern: bool,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct VarData {
    pub ty: Type,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct StructData {
    pub fields: Option<Vec<(String, String)>>,
    pub methods: Option<Vec<String>>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum AssocData {
    Fn(FnData),
    Var(VarData),
    Struct(StructData),
    Module(String),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Symbol {
    pub name: String,
    pub data: AssocData,
}

impl Symbol {
    pub fn new_fn(name: &str, args: &[(String, Type)], ret_ty: &Type, is_extern: bool) -> Self {
        Symbol {
            name: name.to_owned(),
            data: AssocData::Fn(FnData { args: args.to_vec(), ret_ty: ret_ty.to_owned(), is_extern }),
        }
    }

    pub fn new_var(name: &str, ty: &Type) -> Self {
        Symbol { name: name.to_owned(), data: AssocData::Var(VarData { ty: ty.to_owned() }) }
    }

    pub fn new_struct(name: &str, fields: Option<&[(String, String)]>, methods: Option<&[String]>) -> Self {
        Symbol {
            name: name.to_owned(),
            data: AssocData::Struct(StructData {
                fields: fields.map(|x| x.to_vec()),
                methods: methods.map(|x| x.to_vec()),
            }),
        }
    }

    pub fn new_mod(name: &str) -> Self {
        Symbol { name: String::from("module"), data: AssocData::Module(name.to_owned()) }
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

    pub fn fields(&self) -> Option<Vec<(&str, &str)>> {
        match &self.data {
            AssocData::Struct(s) => {
                Some(s.fields.as_deref()?.iter().map(|(n, a)| (n.as_str(), a.as_str())).collect())
            },
            _ => unreachable!("expected symbol to be a struct"),
        }
    }

    pub fn methods(&self) -> Option<Vec<&str>> {
        match &self.data {
            AssocData::Struct(s) => Some(s.methods.as_deref()?.iter().map(|m| m.as_str()).collect()),
            _ => unreachable!("expected symbol to be a struct"),
        }
    }
}

impl Symbolic for Symbol {
    fn name(&self) -> &str {
        &self.name
    }

    fn kind(&self) -> &str {
        match self.data {
            AssocData::Fn(_) => "Fn",
            AssocData::Var(_) => "Var",
            AssocData::Struct(_) => "Struct",
            AssocData::Module(_) => "Module",
        }
    }
}
