use std::{collections::HashMap, fmt::Display};

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

impl Display for SymbolTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let out = self.symbols.keys().zip(self.symbols.values()).fold(
            String::from("Symbol Table\n"),
            |mut acc, (k, v)| {
                acc += &format!("//{}\n{}\n\n", k, v);
                acc
            },
        );

        write!(f, "{}", out)
    }
}

impl Default for SymbolTable {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum Symbol {
    Fn { name: String, args: Vec<Symbol>, ret_ty: Type },
    Var { name: String, ty: Type },
}

impl Symbol {
    pub fn new_fn(name: &str, args: Vec<Symbol>, ret_ty: &Type) -> Self {
        Symbol::Fn { name: name.to_owned(), args, ret_ty: ret_ty.to_owned() }
    }

    pub fn new_var(name: &str, ty: &Type) -> Self {
        Symbol::Var { name: name.to_owned(), ty: ty.to_owned() }
    }

    pub fn ret_ty(&self) -> &Type {
        match self {
            Symbol::Fn { ret_ty, .. } => ret_ty,
            Symbol::Var { .. } => unreachable!("Internal error: expected symbol to be a function"),
        }
    }

    pub fn arg_tys(&self) -> Vec<&Type> {
        match self {
            Symbol::Fn { args, .. } => args.iter().map(|s| s.ty()).collect(),
            Symbol::Var { .. } => unreachable!("Internal error: expected symbol to be a function"),
        }
    }

    pub fn ty(&self) -> &Type {
        match self {
            Symbol::Fn { .. } => unreachable!("Internal error: expected symbol to be a variable"),
            Symbol::Var { ty, .. } => ty,
        }
    }
}

impl Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let out = match self {
            Symbol::Fn { name, args, ret_ty } => {
                let mut fn_str = format!("name: {}\nargs: ", name);
                if args.is_empty() {
                    fn_str += "[]\n";
                } else {
                    fn_str += "[\n";
                    fn_str = args.iter().fold(fn_str, |mut acc, a| {
                        acc += &format!("  {},\n", a);
                        acc
                    });
                    fn_str += "]\n"
                }
                fn_str += &format!("type: {}", ret_ty);
                fn_str
            },
            Symbol::Var { name, ty } => format!("{}: {}", name, ty),
        };

        write!(f, "{}", out)
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

#[cfg(test)]
mod test {
    use crate::{Symbol, SymbolTable, Type};

    #[test]
    fn test_symbol_table() {
        let mut st = SymbolTable::new();

        let fn1 = Symbol::new_fn("foo", vec![], &Type::Void);
        assert_eq!(st.insert("foo", &fn1), None);

        let fn2 = Symbol::new_fn("bar", vec![Symbol::new_var("x", &Type::Int32)], &Type::Void);
        assert_eq!(st.insert("bar", &fn2), None);

        assert!(st.insert("foo", &fn1).is_some());
        assert!(st.exists("bar"));
        assert_eq!(st.get("bar"), Some(&fn2));

        //let fn3 = Symbol::new_fn("foo", vec![], &Type::Bool);
    }
}
