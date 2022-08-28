use std::collections::HashMap;

use crate::Type;

/*
 * scope  name     symbol_ref
 * 0 (global) ---> foo ---> &{...}
 * 1          ---> bar ---> &{...}
 *                 foo ---> &{...}
 */

#[derive(Debug, Clone)]
pub struct SymbolTable<T: Symbolic> {
    tables: HashMap<u32, HashMap<String, T>>,
    scope_depth: u32,
}

impl<T: Symbolic> SymbolTable<T> {
    pub fn new() -> Self {
        let mut tables = HashMap::new();
        tables.insert(0, HashMap::new());
        SymbolTable { tables, scope_depth: 0 }
    }

    pub fn new_with_table(table: HashMap<String, T>) -> Self {
        let mut tables = HashMap::new();
        tables.insert(0, table);
        SymbolTable { tables, scope_depth: 0 }
    }

    pub fn insert(&mut self, name: &str, sym: T) -> Option<T> {
        self.tables
            .get_mut(&self.scope_depth)
            .unwrap_or_else(|| unreachable!("insert at unknown depth"))
            .insert(name.to_owned(), sym)
    }

    pub fn get(&self, name: &str) -> Option<&T> {
        let mut sym = None;
        for depth in (0..=self.scope_depth).rev() {
            let table = self
                .tables
                .get(&depth)
                .unwrap_or_else(|| unreachable!("no table found at scope depth `{}`", depth));
            sym = table.get(name);
            if sym.is_none() {
                if depth == 0 {
                    return None;
                } else {
                    continue;
                }
            } else {
                break;
            }
        }
        sym
    }

    pub fn enter_scope(&mut self) -> u32 {
        self.scope_depth += 1;
        self.tables.insert(self.scope_depth, HashMap::new());
        self.scope_depth
    }

    pub fn leave_scope(&mut self) -> u32 {
        self.tables.remove(&self.scope_depth);
        self.scope_depth -= 1;
        self.scope_depth
    }

    pub fn dump_table(&self, scope: u32) -> Result<(Vec<String>, Vec<T>), String> {
        let table = self.tables.get(&scope).ok_or(format!("can't find table: `{}`", scope))?;
        let keys = table.keys().cloned().collect();
        let values = table.values().cloned().collect();
        Ok((keys, values))
    }
}

impl<T: Symbolic> Default for SymbolTable<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum SymbolKind {
    Var,
    Fn { args: Vec<(String, Type)>, ret_ty: Type },
}

pub trait Symbolic: Clone {
    fn new_fn(name: &str, args: Vec<(String, Type)>, ret_ty: &Type) -> Self;
    fn new_var(name: &str, ty: &Type) -> Self;
    fn name(&self) -> &str;
    fn ty(&self) -> &Type;
    fn kind(&self) -> &SymbolKind;
    fn arg_tys(&self) -> Vec<&Type>;
    fn ret_ty(&self) -> &Type;
}

#[derive(Clone, PartialEq, Debug)]
pub struct Symbol {
    name: String,
    ty: Type,
    kind: SymbolKind,
}

impl Symbolic for Symbol {
    fn new_fn(name: &str, args: Vec<(String, Type)>, ret_ty: &Type) -> Self {
        Symbol {
            name: name.to_owned(),
            ty: Type::Void, // TODO: make fn type
            kind: SymbolKind::Fn { args, ret_ty: ret_ty.to_owned() },
        }
    }

    fn new_var(name: &str, ty: &Type) -> Self {
        Symbol { name: name.to_owned(), ty: ty.to_owned(), kind: SymbolKind::Var }
    }

    fn name(&self) -> &str {
        &self.name
    }

    fn ty(&self) -> &Type {
        &self.ty
    }

    fn kind(&self) -> &SymbolKind {
        &self.kind
    }

    fn arg_tys(&self) -> Vec<&Type> {
        match &self.kind {
            SymbolKind::Fn { args, .. } => args.iter().map(|(_, ty)| ty).collect(),
            SymbolKind::Var => unreachable!("expected symbol to be a function"),
        }
    }

    fn ret_ty(&self) -> &Type {
        match &self.kind {
            SymbolKind::Fn { ret_ty, .. } => ret_ty,
            SymbolKind::Var => unreachable!("expected symbol to be a function"),
        }
    }
}

impl From<(&str, &Type)> for Symbol {
    fn from((name, ty): (&str, &Type)) -> Self {
        Symbol::new_var(name, ty)
    }
}

impl From<&(String, Type)> for Symbol {
    fn from((name, ty): &(String, Type)) -> Self {
        Symbol::new_var(name, ty)
    }
}

pub trait ToSymbol: Clone {
    fn to_symbol(&self) -> Symbol;
}

// Convenience to pass a Symbol directly
impl ToSymbol for Symbol {
    fn to_symbol(&self) -> Symbol {
        self.clone()
    }
}

// For new variables
impl ToSymbol for (&str, &Type) {
    fn to_symbol(&self) -> Symbol {
        Symbol::new_var(self.0, self.1)
    }
}

impl ToSymbol for (String, Type) {
    fn to_symbol(&self) -> Symbol {
        Symbol::new_var(&self.0, &self.1)
    }
}

#[cfg(test)]
mod test {
    use crate::{SymbolTable, ToSymbol, Type, Symbol};

    #[test]
    fn test_symbol_table_scope() {
        let mut st = SymbolTable::<Symbol>::new();

        assert_eq!(st.scope_depth, 0);

        // Insert at global scope
        let var1 = ("foo", &Type::Bool);
        assert_eq!(st.insert("foo", var1.into()), None);
        let sym1 = var1.to_symbol();
        // Get from global scope with new id
        assert_eq!(st.get("foo"), Some(&sym1));

        // Enter scope and insert dup name
        assert_eq!(st.enter_scope(), 1);
        let var2 = ("foo", &Type::Int32);
        assert_eq!(st.insert("foo", var2.into()), None);
        let sym2 = var2.to_symbol();
        // Get dup from new scope with new id
        assert_eq!(st.get("foo"), Some(&sym2));

        // Enter scope and get dup from previous scope with same id
        assert_eq!(st.enter_scope(), 2);
        assert_eq!(st.get("foo"), Some(&sym2));
        // Unknown symbol
        assert_eq!(st.get("bar"), None);
        // Insert new symbol at current scope
        let var3 = ("bar", &Type::Int32);
        assert_eq!(st.insert("bar", var3.into()), None);
        let sym3 = var3.to_symbol();
        // Get new symbol from current scope
        assert_eq!(st.get("bar"), Some(&sym3));
        // Overwrite new symbol with dup at and check that the old symbol is returned
        let var4 = ("bar", &Type::Float);
        assert_eq!(st.insert("bar", var4.into()), Some(sym3));
        // Get dup with new id
        assert_eq!(st.get("bar"), Some(&var4.to_symbol()));

        // Pop scope. Symbols at old scope are gone. Symbols at current scope remain
        assert_eq!(st.leave_scope(), 1);
        assert_eq!(st.get("bar"), None);
        assert_eq!(st.get("foo"), Some(&sym2));

        // Pop scope. Original dup is gone
        assert_eq!(st.leave_scope(), 0);
        assert_eq!(st.get("foo"), Some(&sym1));
    }
}
