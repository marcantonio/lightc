use std::collections::HashMap;

use crate::Type;

#[derive(Debug, Clone)]
pub struct SymbolTable {
    symbols: HashMap<String, Symbol>,
}

impl SymbolTable {
    pub fn new() -> Self {
        SymbolTable { symbols: HashMap::new() }
    }

    // XXX: collisions
    pub fn insert(&mut self, name: &str, sym: &Symbol) -> Option<Symbol> {
        self.symbols.insert(name.to_owned(), sym.to_owned())
    }

    pub fn exists(&self, name: &str) -> bool {
        self.symbols.contains_key(name)
    }

    pub fn get(&self, name: &str) -> Option<&Symbol> {
        self.symbols.get(name)
    }
}

impl Default for SymbolTable {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone, Debug)]
pub enum Symbol {
    Fn { name: String, args: Vec<Symbol>, ret_ty: Type },
    Var { name: String, ty: Type },
}

impl Symbol {
    pub fn new_fn(name: &str, args: Vec<Symbol>, ret_ty: &Type) -> Self {
        Symbol::Fn { name: name.to_owned(), args, ret_ty: ret_ty.to_owned() }
    }

    pub fn ret_ty(&self) -> &Type {
        match self {
            Symbol::Fn { ret_ty, .. } => ret_ty,
            Symbol::Var { .. } => unreachable!("Fatal: Expected symbol to be a function"),
        }
    }

    pub fn arg_tys(&self) -> Vec<&Type> {
        match self {
            Symbol::Fn { args, .. } => args.iter().map(|s| s.ty()).collect(),
            Symbol::Var { .. } => unreachable!("Fatal: Expected symbol to be a function"),
        }
    }

    pub fn ty(&self) -> &Type {
        match self {
            Symbol::Fn { .. } => unreachable!("Fatal: Expected symbol to be a variable"),
            Symbol::Var { ty, .. } => ty,
        }
    }
}

impl From<(&str, &Type)> for Symbol {
    fn from((name, ty): (&str, &Type)) -> Self {
        Symbol::Var { name: name.to_owned(), ty: ty.to_owned() }
    }
}

pub trait SymbolId {
    fn as_symbol_id(&self) -> String;
}
