use std::collections::HashMap;

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
    id_counter: u32,
    scope_depth: u32,
}

impl SymbolTable {
    pub fn new() -> Self {
        let mut table = HashMap::new();
        table.insert(0, HashMap::new());
        SymbolTable { table, id_counter: 0, scope_depth: 0 }
    }

    pub fn insert<T: ToSymbol>(&mut self, name: &str, sym: &T) -> Option<Symbol> {
        let mut sym = sym.to_symbol();
        sym.set_id(self.next_id());

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

    fn next_id(&mut self) -> u32 {
        self.id_counter += 1;
        self.id_counter
    }
}

impl Default for SymbolTable {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct FnSymbol {
    id: u32,
    name: String,
    common_name: String,
    args: Vec<(String, Type)>,
    ret_ty: Type,
}

#[derive(Clone, PartialEq, Debug)]
pub struct VarSymbol {
    id: u32,
    name: String,
    //common_name: String,
    ty: Type,
}

#[derive(Clone, PartialEq, Debug)]
pub enum Symbol {
    Fn(FnSymbol),
    Var(VarSymbol),
}

impl Symbol {
    pub fn new_fn(name: &str, common_name: &str, args: Vec<(String, Type)>, ret_ty: &Type) -> Self {
        Symbol::Fn(FnSymbol {
            id: 0,
            name: name.to_owned(),
            common_name: common_name.to_owned(),
            args,
            ret_ty: ret_ty.to_owned(),
        })
    }

    pub fn new_var(name: &str, ty: &Type) -> Self {
        Symbol::Var(VarSymbol { id: 0, name: name.to_owned(), ty: ty.to_owned() })
    }

    pub fn ty(&self) -> &Type {
        match self {
            Symbol::Fn(_) => unreachable!("expected symbol to be a variable"),
            Symbol::Var(v) => &v.ty,
        }
    }

    pub fn arg_tys(&self) -> Vec<&Type> {
        match self {
            Symbol::Fn(f) => f.args.iter().map(|(_, ty)| ty).collect(),
            Symbol::Var(_) => unreachable!("expected symbol to be a function"),
        }
    }

    pub fn ret_ty(&self) -> &Type {
        match self {
            Symbol::Fn(f) => &f.ret_ty,
            Symbol::Var(_) => unreachable!("expected symbol to be a function"),
        }
    }

    pub fn id(&self) -> u32 {
        match self {
            Symbol::Fn(f) => f.id,
            Symbol::Var(v) => v.id,
        }
    }

    pub fn set_id(&mut self, id: u32) {
        match self {
            Symbol::Fn(f) => f.id = id,
            Symbol::Var(v) => v.id = id,
        }
    }

    pub fn name(&self) -> &str {
        match self {
            Symbol::Fn(f) => &f.name,
            Symbol::Var(v) => &v.name,
        }
    }
}

pub trait ToSymbol: Clone {
    fn to_symbol(&self) -> Symbol;
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
    use crate::{Symbol, SymbolTable, ToSymbol, Type};

    impl Symbol {
        fn with_id(mut self, id: u32) -> Self {
            self.set_id(id);
            self
        }
    }

    impl ToSymbol for Symbol {
        fn to_symbol(&self) -> Symbol {
            self.clone()
        }
    }

    #[test]
    fn test_symbol_table_scope() {
        let mut st = SymbolTable::new();

        assert_eq!(st.scope_depth, 0);

        // Insert at global scope
        let var1 = ("foo", &Type::Bool).to_symbol();
        assert_eq!(st.insert("foo", &var1), None);
        let var1 = var1.with_id(1);
        // Get from global scope with new id
        assert_eq!(st.get("foo"), Some(&var1));

        // Enter scope and insert dup name
        assert_eq!(st.enter_scope(), 1);
        let var2 = ("foo", &Type::Int32).to_symbol();
        assert_eq!(st.insert("foo", &var2), None);
        let var2 = var2.with_id(2);
        // Get dup from new scope with new id
        assert_eq!(st.get("foo"), Some(&var2));

        // Enter scope and get dup from previous scope with same id
        assert_eq!(st.enter_scope(), 2);
        assert_eq!(st.get("foo"), Some(&var2));
        // Unknown symbol
        assert_eq!(st.get("bar"), None);
        // Insert new symbol at current scope
        let var3 = ("bar", &Type::Int32).to_symbol();
        assert_eq!(st.insert("bar", &var3), None);
        let var3 = var3.with_id(3);
        // Get new symbol from current scope
        assert_eq!(st.get("bar"), Some(&var3));
        // Overwrite new symbol with dup at and check that the old symbol is returned
        let var4 = ("bar", &Type::Float).to_symbol();
        assert_eq!(st.insert("bar", &var4), Some(var3));
        // Get dup with new id
        assert_eq!(st.get("bar"), Some(&var4.with_id(4)));

        // Pop scope. Symbols at old scope are gone. Symbols at current scope remain
        assert_eq!(st.leave_scope(), 1);
        assert_eq!(st.get("bar"), None);
        assert_eq!(st.get("foo"), Some(&var2));

        // Pop scope. Original dup is gone
        assert_eq!(st.leave_scope(), 0);
        assert_eq!(st.get("foo"), Some(&var1));
    }
}
