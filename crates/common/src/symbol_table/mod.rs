use std::collections::hash_map::Drain;
use std::collections::HashMap;

pub use symbol::{AssocData, FnData, StructData, Symbol, VarData};

pub mod symbol;

/*
 * scope           name     symbol
 * 0 (global) ---> foo ---> {...}
 * 1          ---> bar ---> {...}
 *                 foo ---> {...}
 * 2          ---> baz ---> {...}
 */

#[derive(Debug, Clone)]
pub struct SymbolTable<T: Symbolic + Ord> {
    tables: HashMap<u32, HashMap<String, T>>,
    scope_depth: u32,
    auto_idents: HashMap<String, u32>,
}

impl<T: Symbolic + Ord> SymbolTable<T> {
    pub fn new() -> Self {
        SymbolTable::with_table(HashMap::new())
    }

    pub fn with_table(table: HashMap<String, T>) -> Self {
        let mut tables = HashMap::new();
        tables.insert(0, table);
        SymbolTable { tables, scope_depth: 0, auto_idents: HashMap::new() }
    }

    pub fn scope_depth(&self) -> u32 {
        self.scope_depth
    }

    pub fn insert(&mut self, sym: T) -> Option<T> {
        self.tables
            .get_mut(&self.scope_depth)
            .unwrap_or_else(|| unreachable!("insert at unknown depth"))
            .insert(sym.name().to_owned(), sym)
    }

    pub fn insert_with_name(&mut self, name: &str, sym: T) -> Option<T> {
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

    pub fn dump_table(&mut self, scope: u32) -> Result<Drain<String, T>, String> {
        let table = self.tables.get_mut(&scope).ok_or(format!("can't find table: `{}`", scope))?;
        Ok(table.drain())
    }

    // Merge globals from other table
    pub fn merge_symbols(&mut self, other: &mut SymbolTable<T>) -> Result<(), String> {
        let symbols = other.dump_table(0)?;
        for (name, symbol) in symbols {
            if name != "module" && self.insert_with_name(&name, symbol).is_some() {
                return Err(format!("can't redefine `{}`", name));
            }
        }
        Ok(())
    }

    pub fn export_symbols(&self) -> Vec<&T> {
        let mut symbols = self
            .tables
            .get(&0)
            .unwrap_or_else(|| unreachable!("No global scope in `export_symbols()`"))
            .values()
            // TODO: limit this to exportables
            .filter(|sym| sym.name().starts_with("_"))
            .collect::<Vec<_>>();
        symbols.sort();
        symbols.dedup();
        symbols
    }

    pub fn types(&self) -> Vec<String> {
        self.tables
            .get(&0)
            .unwrap_or_else(|| unreachable!("No global scope in `types()`"))
            .values()
            .filter(|sym| sym.kind() == "Struct")
            .map(|sym| sym.name().to_owned())
            .collect()
    }

    // Pick a new unique identifier
    pub fn uniq_ident(&mut self, name: Option<&str>) -> String {
        let name = match name {
            Some(n) => format!("_{}", n),
            None => String::from("_light_intern"),
        };

        let ver = self.auto_idents.entry(name.to_owned()).or_insert(0);
        *ver += 1;
        format!("{}@{}", name, ver)
    }
}

impl<T: Symbolic + Ord> Default for SymbolTable<T> {
    fn default() -> Self {
        Self::new()
    }
}

pub trait Symbolic {
    fn name(&self) -> &str;
    fn kind(&self) -> &str;
}

#[cfg(test)]
mod test {
    use crate::Type;
    use crate::{Symbol, SymbolTable};

    #[test]
    fn test_symbol_table_scope() {
        let mut st = SymbolTable::<Symbol>::new();

        assert_eq!(st.scope_depth, 0);

        // Insert at global scope
        let sym1 = Symbol::new_var("foo", &Type::Bool);
        assert_eq!(st.insert(sym1.clone()), None);
        // Get from global scope
        assert_eq!(st.get("foo"), Some(&sym1));

        // Enter scope and insert dup name
        assert_eq!(st.enter_scope(), 1);
        let sym2 = Symbol::new_var("foo", &Type::Int32);
        assert_eq!(st.insert(sym2.clone()), None);
        // Get dup from new scope
        assert_eq!(st.get("foo"), Some(&sym2));

        // Enter scope and get dup from previous scope
        assert_eq!(st.enter_scope(), 2);
        assert_eq!(st.get("foo"), Some(&sym2));
        // Unknown symbol
        assert_eq!(st.get("bar"), None);
        // Insert new symbol at current scope
        let sym3 = Symbol::new_var("bar", &Type::Int32);
        assert_eq!(st.insert(sym3.clone()), None);
        // Get new symbol from current scope
        assert_eq!(st.get("bar"), Some(&sym3));
        // Overwrite new symbol with dup at and check that the old symbol is returned
        let sym4 = Symbol::new_var("bar", &Type::Float);
        assert_eq!(st.insert(sym4.clone()), Some(sym3));
        // Get dup with new id
        assert_eq!(st.get("bar"), Some(&sym4));

        // Pop scope. Symbols at old scope are gone. Symbols at current scope remain
        assert_eq!(st.leave_scope(), 1);
        assert_eq!(st.get("bar"), None);
        assert_eq!(st.get("foo"), Some(&sym2));

        // Pop scope. Original dup is gone
        assert_eq!(st.leave_scope(), 0);
        assert_eq!(st.get("foo"), Some(&sym1));
    }

    #[test]
    fn test_uniq_ident() {
        let mut st = SymbolTable::<Symbol>::new();
        assert_eq!(st.uniq_ident(Some("foo")), String::from("_foo@1"));
        assert_eq!(st.uniq_ident(Some("foo")), String::from("_foo@2"));
        assert_eq!(st.uniq_ident(None), String::from("_light_intern@1"));
        assert_eq!(st.uniq_ident(None), String::from("_light_intern@2"));
    }

    #[test]
    fn test_merge_symbols() {
        let mut a = SymbolTable::<Symbol>::new();
        let mut b = SymbolTable::<Symbol>::new();

        let sym1 = Symbol::new_var("foo", &Type::Bool);
        a.insert(sym1.clone());
        let sym2 = Symbol::new_var("bar", &Type::Bool);
        a.insert(sym2.clone());

        let sym3 = Symbol::new_var("baz", &Type::Bool);
        b.insert(sym3.clone());

        assert_eq!(b.merge_symbols(&mut a), Ok(()));
        assert_eq!(b.get("foo"), Some(&sym1));
        assert_eq!(b.get("bar"), Some(&sym2));
        assert_eq!(b.get("baz"), Some(&sym3));
    }

        #[test]
    fn test_merge_symbols_dup() {
        let mut a = SymbolTable::<Symbol>::new();
        let mut b = SymbolTable::<Symbol>::new();

        a.insert(Symbol::new_var("foo", &Type::Bool));
        b.insert(Symbol::new_var("foo", &Type::Bool));

        assert_eq!(b.merge_symbols(&mut a), Err(String::from("can't redefine `foo`")));
    }

}
