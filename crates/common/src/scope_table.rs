use std::collections::HashMap;

#[derive(Debug)]
pub struct ScopeTable<T> {
    table: HashMap<i32, HashMap<String, T>>,
    depth: i32,
}

impl<T: Clone> ScopeTable<T> {
    pub fn new() -> Self {
        let mut table = HashMap::new();
        table.insert(0, HashMap::new());
        ScopeTable { table, depth: 0 }
    }

    // Drop down 1 scope level
    pub fn down_scope(&mut self) -> i32 {
        self.depth += 1;
        self.table.insert(self.depth, HashMap::new());
        self.depth
    }

    // Pop up 1 scope level
    pub fn up_scope(&mut self) -> Result<i32, String> {
        self.table.remove(&self.depth);
        self.depth -= 1;
        if self.depth < 0 {
            return Err("Internal error: Symbol table below 0".to_string());
        }
        Ok(self.depth)
    }

    // Insert symbol at current scope depth
    pub fn insert(&mut self, name: &str, sym: T) -> Result<(), String> {
        let cur = self
            .table
            .get_mut(&self.depth)
            .unwrap_or_else(|| panic!("Internal error: insert at unknown depth"));
        cur.insert(name.to_owned(), sym);
        Ok(())
    }

    // Remove symbol at current scope depth
    pub fn remove(&mut self, name: &str) -> Option<T> {
        let cur = self
            .table
            .get_mut(&self.depth)
            .unwrap_or_else(|| panic!("Internal error: remove at unknown depth"));
        cur.remove(name)
    }

    // Starting at the current scope depth, locate `name`. Keep walking up the
    // tables.
    pub fn get(&self, name: &str) -> Option<T> {
        let mut sym = None;
        for depth in (0..=self.depth).rev() {
            let table = self
                .table
                .get(&depth)
                .unwrap_or_else(|| panic!("Internal error: No table found at depth `{}`", depth));
            sym = table.get(name).cloned();
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
}

impl<T: Clone> Default for ScopeTable<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod test {
    use crate::{ScopeTable, Type};

    #[test]
    fn test_scope_table() {
        let mut st = ScopeTable::new();
        assert_eq!(st.depth, 0);
        assert_eq!(st.insert("foo", Type::Bool), Ok(()));
        assert_eq!(st.get("foo"), Some(Type::Bool));
        assert_eq!(st.down_scope(), 1);
        assert_eq!(st.insert("foo", Type::Int32), Ok(()));
        assert_eq!(st.down_scope(), 2);
        assert_eq!(st.get("foo"), Some(Type::Int32));
        assert_eq!(st.get("bar"), None);
        assert_eq!(st.up_scope(), Ok(1));
        assert_eq!(st.get("foo"), Some(Type::Int32));
        assert_eq!(st.up_scope(), Ok(0));
        assert_eq!(st.get("foo"), Some(Type::Bool));
        assert_eq!(st.remove("foo"), Some(Type::Bool));
        assert_eq!(st.remove("foo"), None);
        assert_eq!(st.get("foo"), None);
    }
}
