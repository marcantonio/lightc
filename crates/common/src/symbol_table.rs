use std::collections::HashMap;

#[derive(Debug)]
pub struct SymbolTable<T> {
    table: HashMap<i32, HashMap<String, T>>, // XXX &str
    depth: i32,
}

impl<T: Clone> SymbolTable<T> {
    pub fn new() -> Self {
        let mut table = HashMap::new();
        table.insert(0, HashMap::new());
        SymbolTable { table, depth: 0 }
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
            return Err("NONCANBE: Symbol table below 0".to_string());
        }
        Ok(self.depth)
    }

    // Insert symbol at current scope depth
    pub fn insert(&mut self, name: &str, ty: T) -> Result<(), String> {
        let cur = self.table.get_mut(&self.depth).ok_or("Unknown depth")?;
        cur.insert(name.to_owned(), ty);
        Ok(())
    }

    // Remove symbol at current scope depth
    pub fn remove(&mut self, name: &str) -> Option<T> {
        let cur = self.table.get_mut(&self.depth).unwrap(); //.ok_or("Unknown depth"); // NONCANBE
        cur.remove(name)
    }

    // Starting at the current scope depth, locate `name`. Keep walking up the
    // tables.
    pub fn get(&self, name: &str) -> Option<T> {
        let mut ty = None;
        for depth in (0..=self.depth).rev() {
            let table = self
                .table
                .get(&depth)
                .unwrap_or_else(|| panic!("NONCANBE: No table found at depth `{}`", depth));
            ty = table.get(name).cloned();
            if ty.is_none() {
                if depth == 0 {
                    return None;
                } else {
                    continue;
                }
            } else {
                break;
            }
        }
        ty
    }
}

impl<T: Clone> Default for SymbolTable<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod test {
    use crate::{symbol_table::SymbolTable, Type};


    #[test]
    fn test_st() {
        let mut st = SymbolTable::new();
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
