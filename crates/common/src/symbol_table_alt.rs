use std::{collections::HashMap, fmt::Display};

use crate::Type;

/*
 * Variant on a LeBlanc-Cook style symbol table. The vector of symbols at end the leaves
 * makes it overly complex. This is necessary so as not to overwrite any symbols. I think
 * we'll need this for analysis later.
 *
 * Structure
 * name     scope     symbol
 * foo ---> 1 ------> [ {...} ]
 *          2 ------> [ {...} ]
 * bar ---> 2 ------> [ {...}, {...} ]
 *
 *
 * TODO: Re-evaluate. This is probably overdone, but I keep going back and forth. This
 * implementation remembers every declaration in every scope. That feels like overkill. I
 * had a much simpler "scope table" implementation that dynamically created a new hashmap
 * for each scope. It worked well, but wasn't good enough for forward declarations because
 * of it's ephemerality. This is the other extreme.
 */

#[derive(Debug, Clone)]
pub struct SymbolTableAlt {
    symbols: HashMap<String, HashMap<u32, Vec<SymbolAlt>>>,
    scope_stack: Vec<u32>,
    scope_counter: u32,
    next_id: u32,
}

impl SymbolTableAlt {
    pub fn new() -> Self {
        SymbolTableAlt { symbols: HashMap::new(), scope_stack: vec![0], scope_counter: 0, next_id: 0 }
    }

    // Inserts symbol into proper name/scope table. Returns the previous symbol if a dup,
    // or None if new.
    pub fn insert<T: ToSymbolAlt>(&mut self, name: &str, sym: &T) -> Option<SymbolAlt> {
        let mut sym = sym.to_symbol();
        sym.id = self.next_id();
        sym.scope = *self.scope_stack.last().unwrap();

        match self.symbols.get_mut(name) {
            Some(scope_table) => match scope_table.get_mut(&sym.scope) {
                Some(sym_list) => {
                    let old = sym_list.last().cloned();
                    sym_list.push(sym);
                    old
                },
                None => {
                    scope_table.insert(sym.scope, vec![sym]);
                    None
                },
            },
            None => {
                let mut name_table = HashMap::new();
                name_table.insert(sym.scope, vec![sym]);
                self.symbols.insert(name.to_owned(), name_table);
                None
            },
        }

        // TODO: Cleaner but doesn't indicate if the symbol was previously present.
        // What a mess :). Inserts a new HashMap if there is no name table present. Then
        // it checks for the scope table. It either inserts one with the new vector
        // containing sym as a value, or pushes sym onto the existing vector. Finally, it
        // returns a clone of the sym with the scope and id filled in.
        // self.symbols
        //     .entry(name.to_owned())
        //     .or_insert_with(HashMap::new)
        //     .entry(sym.scope)
        //     .and_modify(|e| e.push(sym.clone()))
        //     .or_insert(vec![sym])
        //     .last()
        //     .cloned()
    }

    pub fn exists(&self, name: &str) -> bool {
        self.symbols.contains_key(name)
    }

    pub fn get(&self, name: &str) -> Option<&SymbolAlt> {
        let chain = self.symbols.get(name)?;
        self.scope_stack.iter().rev().find_map(|s| {
            chain.get(s).map(|v| v.last().unwrap_or_else(|| unreachable!("no last element in symbol vector")))
        })
    }

    pub fn enter_scope(&mut self) -> u32 {
        self.scope_counter += 1;
        self.scope_stack.push(self.scope_counter);
        self.scope_counter
    }

    pub fn leave_scope(&mut self) -> u32 {
        let old_scope = self.scope_stack.pop().unwrap_or_else(|| unreachable!("can't leave global scope"));
        if old_scope == 0 {
            unreachable!("can't leave global scope");
        }
        old_scope
    }

    pub fn reset_scope_counter(&mut self) {
        self.scope_counter = 0;
    }

    fn next_id(&mut self) -> u32 {
        let cur = self.next_id;
        self.next_id += 1;
        cur
    }
}

impl Display for SymbolTableAlt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut out = format!(
            "===Symbol Table===\nscope_counter: {}\nnext_id: {}\nscope_stack: ",
            self.scope_counter, self.next_id
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
                v.keys().zip(v.values()).for_each(|(scope, symbols)| {
                    acc += &format!("{} -> ({} -> ", name, scope);
                    symbols.iter().for_each(|sym| acc += &format!("{{ {} }}, ", sym));
                    acc = acc.trim_end_matches(", ").to_string();
                    acc += ")\n";
                });
                acc
            },
        );

        write!(f, "{}", out)
    }
}

impl Default for SymbolTableAlt {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum SymbolKind {
    Var,
    Fn(Vec<SymbolAlt>),
}

#[derive(Clone, PartialEq, Debug)]
pub struct SymbolAlt {
    id: u32,
    name: String,
    ty: Type,
    scope: u32,
    kind: SymbolKind,
}

impl SymbolAlt {
    pub fn new_fn(name: &str, args: Vec<SymbolAlt>, ty: &Type) -> Self {
        SymbolAlt { id: 0, name: name.to_owned(), scope: 0, ty: ty.to_owned(), kind: SymbolKind::Fn(args) }
    }

    pub fn new_var(name: &str, ty: &Type) -> Self {
        SymbolAlt { id: 0, name: name.to_owned(), scope: 0, ty: ty.to_owned(), kind: SymbolKind::Var }
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

impl Display for SymbolAlt {
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

pub trait ToSymbolAlt: Clone {
    fn to_symbol(&self) -> SymbolAlt;
}

// For new variables
impl ToSymbolAlt for (&str, &Type) {
    fn to_symbol(&self) -> SymbolAlt {
        SymbolAlt::new_var(self.0, self.1)
    }
}

impl ToSymbolAlt for (String, Type) {
    fn to_symbol(&self) -> SymbolAlt {
        SymbolAlt::new_var(&self.0, &self.1)
    }
}

// impl ToSymbolAlt for Prototype {
//     fn to_symbol(&self) -> SymbolAlt {
//         SymbolAlt::new_fn(
//             self.name(),
//             // XXX: ignore these for now. Maybe this should just be types and not symbols,
//             // i.e., a signature?
//             self.args().iter().map(|(name, ty)| (name.as_ref(), ty).to_symbol()).collect::<Vec<SymbolAlt>>(),
//             self.ret_ty().unwrap_or_default(),
//         )
//     }
// }

#[cfg(test)]
mod test {
    use crate::{symbol_table_alt::SymbolTableAlt, Type};

    use super::{SymbolAlt, ToSymbolAlt};

    impl SymbolAlt {
        fn with_id(mut self, id: u32) -> Self {
            self.id = id;
            self
        }

        fn with_scope(mut self, scope: u32) -> Self {
            self.scope = scope;
            self
        }
    }

    impl ToSymbolAlt for SymbolAlt {
        fn to_symbol(&self) -> SymbolAlt {
            self.clone()
        }
    }

    #[test]
    fn test_alt_symbol_table_fn() {
        let mut st = SymbolTableAlt::new();

        let fn1 = SymbolAlt::new_fn("foo", vec![], &Type::Void);
        assert_eq!(st.insert("foo", &fn1), None);

        let fn2 = SymbolAlt::new_fn(
            "bar",
            vec![SymbolAlt::new_var("x", &Type::Int32), SymbolAlt::new_var("y", &Type::Int32)],
            &Type::Void,
        );
        assert_eq!(st.insert("bar", &fn2), None);

        // should not stop fn redefinition here
        let fn3 = SymbolAlt::new_fn("foo", vec![], &Type::Bool);
        assert!(st.insert("foo", &fn3).is_some());
        assert_eq!(st.get("foo"), Some(&fn3.with_id(2).with_scope(0)));
        assert_eq!(st.get("bar"), Some(&fn2.with_id(1).with_scope(0)));
    }

    #[test]
    fn test_alt_symbol_table_dup() {
        let mut st = SymbolTableAlt::new();

        st.enter_scope();
        let var = SymbolAlt::new_var("foo", &Type::Bool);
        st.insert("foo", &var);

        st.enter_scope();
        let var = SymbolAlt::new_var("foo", &Type::Int32);
        let var_copy = var.clone();
        st.insert("foo", &var);
        assert_eq!(st.get("foo"), Some(&var.with_id(1).with_scope(2)));

        let fn1 = SymbolAlt::new_fn("foo", vec![], &Type::Void);
        st.insert("foo", &fn1);
        assert_ne!(st.get("foo"), Some(&var_copy));
    }

    #[test]
    fn test_alt_symbol_table_scope() {
        let mut st = SymbolTableAlt::new();

        let fn1 = SymbolAlt::new_fn("globalFn1", vec![], &Type::Void);
        assert_eq!(st.insert("globalFn1", &fn1), None);

        st.enter_scope();
        let foo1 = SymbolAlt::new_var("foo", &Type::Bool);
        st.insert("foo", &foo1);
        let bar1 = SymbolAlt::new_var("bar", &Type::Float);
        st.insert("bar", &bar1);

        st.enter_scope();
        let foo2 = SymbolAlt::new_var("foo", &Type::Float);
        st.insert("foo", &foo2);
        st.insert("baz", &SymbolAlt::new_var("baz", &Type::Float));
        assert_eq!(st.get("foo"), Some(&foo2.with_id(3).with_scope(2)));
        assert_eq!(st.get("bar"), Some(&bar1.with_id(2).with_scope(1)));

        st.leave_scope();
        assert_eq!(st.get("foo"), Some(&foo1.with_id(1).with_scope(1)));
        assert_eq!(st.get("baz"), None);

        st.enter_scope();
        let bar2 = SymbolAlt::new_var("bar", &Type::Bool);
        st.insert("bar", &bar2);
        assert_eq!(st.get("bar"), Some(&bar2.with_id(5).with_scope(3)));

        assert_eq!(st.leave_scope(), 3);
        assert_eq!(st.leave_scope(), 1);

        let fn2 = SymbolAlt::new_fn("globalFn2", vec![], &Type::Void);
        assert_eq!(st.insert("globalFn2", &fn2), None);

        assert_eq!(st.get("globalFn2"), Some(&fn2.with_id(6)))
    }

    #[test]
    fn test_alt_symbol_table_shadowing() {
        let mut st = SymbolTableAlt::new();

        let foo1 = SymbolAlt::new_var("foo1", &Type::Void);
        st.insert("foo1", &foo1);
    }

    #[test]
    fn test_alt_symbol_table_dup_in_scope() {
        let mut st = SymbolTableAlt::new();

        st.enter_scope();
        let foo1 = SymbolAlt::new_var("foo", &Type::Bool);
        st.insert("foo", &foo1);
        let foo2 = SymbolAlt::new_var("foo", &Type::Float);
        st.insert("foo", &foo2);
        assert_eq!(st.get("foo"), Some(&foo2.clone().with_id(1).with_scope(1)));
        assert_eq!(st.get("foo"), Some(&foo2.with_id(1).with_scope(1)));
    }

    #[test]
    #[should_panic(expected = "internal error: entered unreachable code: can't leave global scope")]
    fn test_alt_symbol_table_scope_panic() {
        let mut st = SymbolTableAlt::new();
        assert_eq!(st.enter_scope(), 1);
        assert_eq!(st.leave_scope(), 1);
        assert_eq!(st.leave_scope(), 0); // error
    }
}
