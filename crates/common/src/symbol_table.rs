use std::{collections::HashMap, fmt::Display};

use crate::Type;

// LeBlanc-Cook style symbol table
#[derive(Debug, Clone)]
pub struct SymbolTable {
    symbols: HashMap<String, HashMap<u32, Symbol>>,
    scope_stack: Vec<u32>,
    cur_scope: u32,
    next_id: u32,
}

pub trait ToSymbol: Clone {
    fn to_symbol(&self) -> Symbol;
}

impl SymbolTable {
    pub fn new() -> Self {
        SymbolTable { symbols: HashMap::new(), scope_stack: vec![0], cur_scope: 0, next_id: 0 }
    }

    pub fn insert<T: ToSymbol>(&mut self, name: &str, sym: &T) -> Option<Symbol> {
        let mut sym = sym.to_symbol();
        sym.id = self.next_id();
        sym.scope = self.cur_scope;

        self.symbols.entry(name.to_owned()).or_insert_with(HashMap::new).insert(sym.scope, sym)
    }

    pub fn exists(&self, name: &str) -> bool {
        self.symbols.contains_key(name)
    }

    pub fn get(&self, name: &str) -> Option<&Symbol> {
        let chain = self.symbols.get(name)?;
        self.scope_stack.iter().rev().find_map(|s| chain.get(s))
    }

    pub fn enter_scope(&mut self) -> u32 {
        self.cur_scope += 1;
        self.scope_stack.push(self.cur_scope);
        self.cur_scope
    }

    pub fn leave_scope(&mut self) -> u32 {
        self.scope_stack.pop();
        self.cur_scope =
            self.scope_stack.last().copied().unwrap_or_else(|| unreachable!("can't leave global scope"));
        self.cur_scope
    }

    fn next_id(&mut self) -> u32 {
        self.next_id += 1;
        self.next_id
    }
}

impl Display for SymbolTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut out = format!(
            "===Symbol Table===\ncur_scope: {}\nnext_id: {}\nscope_stack: ",
            self.cur_scope, self.next_id
        );

        if self.scope_stack.is_empty() {
            out += "[]";
        } else {
            out += &self.scope_stack[1..].iter().fold(format!("[{}", self.scope_stack[0]), |mut acc, v| {
                acc += &format!(", {}", v);
                acc
            });
        }

        out += &self.symbols.keys().zip(self.symbols.values()).fold(
            String::from("]\nsymbols:\n"),
            |mut acc, (name, v)| {
                v.keys()
                    .zip(v.values())
                    .for_each(|(scope, symbol)| acc += &format!("{} -> ({} -> {})\n", name, scope, symbol));
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
pub enum SymbolKind {
    Var,
    Fn(Vec<Symbol>),
}

#[derive(Clone, PartialEq, Debug)]
pub struct Symbol {
    id: u32,
    name: String,
    ty: Type,
    scope: u32,
    kind: SymbolKind,
}

impl Symbol {
    pub fn new_fn(name: &str, args: Vec<Symbol>, ty: &Type) -> Self {
        Symbol { id: 0, name: name.to_owned(), scope: 0, ty: ty.to_owned(), kind: SymbolKind::Fn(args) }
    }

    pub fn new_var(name: &str, ty: &Type) -> Self {
        Symbol { id: 0, name: name.to_owned(), scope: 0, ty: ty.to_owned(), kind: SymbolKind::Var }
    }

    pub fn ty(&self) -> &Type {
        &self.ty
    }

    pub fn arg_tys(&self) -> Vec<&Type> {
        match &self.kind {
            SymbolKind::Var => unreachable!("expected symbol to be a function"),
            SymbolKind::Fn(args) => args.iter().map(|s| s.ty()).collect(),
        }
    }
}

impl Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let out = match &self.kind {
            SymbolKind::Fn(args) => {
                let mut fn_str = format!(
                    "id: {}, name: {}, type: {}, scope: {}, kind: fn, args: ",
                    self.id, self.name, self.ty, self.scope,
                );
                if args.is_empty() {
                    fn_str += "[]";
                } else {
                    fn_str += "[\n";
                    fn_str = args.iter().fold(fn_str, |mut acc, a| {
                        acc += &format!("  {}\n", a);
                        acc
                    });
                    fn_str += "]";
                }
                fn_str
            },
            SymbolKind::Var => {
                format!(
                    "id: {}, name: {}, type: {}, scope: {}, kind: var",
                    self.id, self.name, self.ty, self.scope
                )
            },
        };

        write!(f, "{}", out)
    }
}

impl From<(&str, &Type)> for Symbol {
    fn from((name, ty): (&str, &Type)) -> Self {
        Symbol::new_var(name, ty)
    }
}

#[cfg(test)]
mod test {
    use crate::{Symbol, SymbolTable, ToSymbol, Type};

    impl Symbol {
        fn with_id(mut self, id: u32) -> Self {
            self.id = id;
            self
        }

        fn with_scope(mut self, scope: u32) -> Self {
            self.scope = scope;
            self
        }
    }

    impl ToSymbol for Symbol {
        fn to_symbol(&self) -> Symbol {
            self.clone()
        }
    }

    #[test]
    fn test_symbol_table_fn() {
        let mut st = SymbolTable::new();

        let fn1 = Symbol::new_fn("foo", vec![], &Type::Void);
        assert_eq!(st.insert("foo", &fn1), None);

        let fn2 = Symbol::new_fn(
            "bar",
            vec![Symbol::new_var("x", &Type::Int32), Symbol::new_var("y", &Type::Int32)],
            &Type::Void,
        );
        assert_eq!(st.insert("bar", &fn2), None);

        // should not stop fn redefinition here
        let fn3 = Symbol::new_fn("foo", vec![], &Type::Bool);
        assert!(st.insert("foo", &fn3).is_some());
        assert_eq!(st.get("foo"), Some(&fn3.with_id(3).with_scope(0)));

        assert_eq!(st.get("bar"), Some(&fn2.with_id(2).with_scope(0)));
    }

    #[test]
    fn test_symbol_table_dup() {
        let mut st = SymbolTable::new();

        st.enter_scope();
        let var = Symbol::new_var("foo", &Type::Bool);
        st.insert("foo", &var);

        st.enter_scope();
        let var = Symbol::new_var("foo", &Type::Int32);
        let var_copy = var.clone();
        st.insert("foo", &var);
        assert_eq!(st.get("foo"), Some(&var.with_id(2).with_scope(2)));

        let fn1 = Symbol::new_fn("foo", vec![], &Type::Void);
        st.insert("foo", &fn1);
        assert_ne!(st.get("foo"), Some(&var_copy));
    }

    #[test]
    fn test_symbol_table_scope() {
        let mut st = SymbolTable::new();

        st.enter_scope();
        let foo1 = Symbol::new_var("foo", &Type::Bool);
        st.insert("foo", &foo1);
        let bar1 = Symbol::new_var("bar", &Type::Float);
        st.insert("bar", &bar1);

        st.enter_scope();
        let foo2 = Symbol::new_var("foo", &Type::Float);
        st.insert("foo", &foo2);
        st.insert("baz", &Symbol::new_var("baz", &Type::Float));
        assert_eq!(st.get("foo"), Some(&foo2.with_id(3).with_scope(2)));
        assert_eq!(st.get("bar"), Some(&bar1.with_id(2).with_scope(1)));

        st.leave_scope();
        assert_eq!(st.get("foo"), Some(&foo1.with_id(1).with_scope(1)));
        assert_eq!(st.get("baz"), None);

        assert_eq!(st.leave_scope(), 0);
    }

    #[test]
    #[should_panic(expected = "internal error: entered unreachable code: can't leave global scope")]
    fn test_symbol_table_scope_panic() {
        let mut st = SymbolTable::new();
        assert_eq!(st.enter_scope(), 1);
        assert_eq!(st.leave_scope(), 0);
        assert_eq!(st.leave_scope(), 0); // error
    }
}
