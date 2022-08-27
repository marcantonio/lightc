use std::{collections::HashMap, fmt::Debug};

use crate::Type;

/*
 * scope  name     symbol_ref
 * 0 (global) ---> foo ---> &{...}
 * 1          ---> bar ---> &{...}
 *                 foo ---> &{...}
 */

#[derive(Debug, Clone)]
pub struct SymbolTable {
    table: HashMap<u32, HashMap<String, Symbol>>,
    scope_depth: u32,
}

impl SymbolTable {
    pub fn new() -> Self {
        let mut table = HashMap::new();
        table.insert(0, HashMap::new());
        SymbolTable { table, scope_depth: 0 }
    }

    pub fn insert<T: ToSymbol>(&mut self, name: &str, sym: T) -> Option<Symbol> {
        let sym = sym.to_symbol();

        self.table
            .get_mut(&self.scope_depth)
            .unwrap_or_else(|| unreachable!("insert at unknown depth"))
            .insert(name.to_owned(), sym)
    }

    pub fn get(&self, name: &str) -> Option<&Symbol> {
        let mut sym = None;
        for depth in (0..=self.scope_depth).rev() {
            let table = self
                .table
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
        self.table.insert(self.scope_depth, HashMap::new());
        self.scope_depth
    }

    pub fn leave_scope(&mut self) -> u32 {
        self.table.remove(&self.scope_depth);
        self.scope_depth -= 1;
        self.scope_depth
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
    Fn { args: Vec<(String, Type)>, ret_ty: Type },
}

#[derive(Clone, PartialEq, Debug)]
pub struct Symbol {
    name: String,
    ty: Type,
    kind: SymbolKind,
    pub pointer_value: *const i64,
}

impl Symbol {
    pub fn new_fn(name: &str, args: Vec<(String, Type)>, ret_ty: &Type) -> Self {
        Symbol {
            name: name.to_owned(),
            ty: Type::Void, // TODO: make fn type
            kind: SymbolKind::Fn { args, ret_ty: ret_ty.to_owned() },
            pointer_value: &0,
        }
    }

    pub fn new_var(name: &str, ty: &Type) -> Self {
        Symbol { name: name.to_owned(), ty: ty.to_owned(), kind: SymbolKind::Var, pointer_value: &0 }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn ty(&self) -> &Type {
        &self.ty
    }

    pub fn arg_tys(&self) -> Vec<&Type> {
        match &self.kind {
            SymbolKind::Fn { args, .. } => args.iter().map(|(_, ty)| ty).collect(),
            SymbolKind::Var => unreachable!("expected symbol to be a function"),
        }
    }

    pub fn ret_ty(&self) -> &Type {
        match &self.kind {
            SymbolKind::Fn { ret_ty, .. } => ret_ty,
            SymbolKind::Var => unreachable!("expected symbol to be a function"),
        }
    }
}

pub trait ToSymbol: Clone {
    fn to_symbol(self) -> Symbol;
}

// Convenience to pass a Symbol directly
impl ToSymbol for Symbol {
    fn to_symbol(self) -> Symbol {
        self
    }
}

// For new variables
impl ToSymbol for (&str, &Type) {
    fn to_symbol(self) -> Symbol {
        Symbol::new_var(self.0, self.1)
    }
}

impl ToSymbol for (String, Type) {
    fn to_symbol(self) -> Symbol {
        Symbol::new_var(&self.0, &self.1)
    }
}

#[cfg(test)]
mod test {
    use crate::{SymbolTable, ToSymbol, Type};

    #[test]
    fn test_symbol_table_scope() {
        let mut st = SymbolTable::new();

        assert_eq!(st.scope_depth, 0);

        // Insert at global scope
        let var1 = ("foo", &Type::Bool);
        assert_eq!(st.insert("foo", var1), None);
        let sym1 = var1.to_symbol();
        // Get from global scope with new id
        assert_eq!(st.get("foo"), Some(&sym1));

        // Enter scope and insert dup name
        assert_eq!(st.enter_scope(), 1);
        let var2 = ("foo", &Type::Int32);
        assert_eq!(st.insert("foo", var2), None);
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
        assert_eq!(st.insert("bar", var3), None);
        let sym3 = var3.to_symbol();
        // Get new symbol from current scope
        assert_eq!(st.get("bar"), Some(&sym3));
        // Overwrite new symbol with dup at and check that the old symbol is returned
        let var4 = ("bar", &Type::Float);
        assert_eq!(st.insert("bar", var4), Some(sym3));
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
