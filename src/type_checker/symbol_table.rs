use std::collections::HashMap;

use crate::token::Type;

#[derive(Debug)]
pub(crate) struct SymbolTable {
    table: HashMap<i32, HashMap<String, Type>>,
    depth: i32,
}

impl SymbolTable {
    pub(crate) fn new() -> Self {
        let mut table = HashMap::new();
        table.insert(0, HashMap::new());
        SymbolTable { table, depth: 0 }
    }

    // Drop down 1 scope level
    pub(crate) fn down_scope(&mut self) -> i32 {
        self.depth += 1;
        self.table.insert(self.depth, HashMap::new());
        self.depth
    }

    // Pop up 1 scope level
    pub(crate) fn up_scope(&mut self) -> Result<i32, String> {
        self.table.remove(&self.depth);
        self.depth -= 1;
        if self.depth < 0 {
            return Err("NONCANBE: Symbol table below 0".to_string());
        }
        Ok(self.depth)
    }

    // Insert symbol at current scope depth
    pub(crate) fn insert(&mut self, name: &str, ty: Type) -> Result<(), String> {
        let cur = self.table.get_mut(&self.depth).ok_or("Unknown depth")?;
        cur.insert(name.to_owned(), ty);
        Ok(())
    }

    // Remove symbol at current scope depth
    pub(crate) fn remove(&mut self, name: &str) -> Option<Type> {
        let cur = self.table.get_mut(&self.depth).unwrap(); //.ok_or("Unknown depth"); // NONCANBE
        cur.remove(name)
    }

    // Starting at the current scope depth, locate `name`. Keep walking up the
    // tables.
    pub(crate) fn get(&self, name: &str) -> Result<Type, String> {
        let mut ty = None;
        for depth in (0..=self.depth).rev() {
            let table = self
                .table
                .get(&depth)
                .ok_or(format!("NONCANBE: No table found at depth `{}`", depth))?;
            ty = table.get(name).cloned();
            if ty.is_none() {
                if depth == 0 {
                    return Err(format!("Symbol `{}` not found in table", name));
                } else {
                    continue;
                }
            } else {
                break;
            }
        }
        Ok(ty.unwrap())
    }
}

#[cfg(test)]
mod test {
    use crate::{token::Type, type_checker::symbol_table::SymbolTable};

    #[test]
    fn test_st() {
        let mut st = SymbolTable::new();
        assert_eq!(st.depth, 0);
        assert_eq!(st.insert("foo", Type::Bool), Ok(()));
        assert_eq!(st.get("foo"), Ok(Type::Bool));
        assert_eq!(st.down_scope(), 1);
        assert_eq!(st.insert("foo", Type::Int32), Ok(()));
        assert_eq!(st.down_scope(), 2);
        assert_eq!(st.get("foo"), Ok(Type::Int32));
        assert_eq!(
            st.get("bar"),
            Err("Symbol `bar` not found in table".to_string())
        );
        assert_eq!(st.up_scope(), Ok(1));
        assert_eq!(st.get("foo"), Ok(Type::Int32));
        assert_eq!(st.up_scope(), Ok(0));
        assert_eq!(st.get("foo"), Ok(Type::Bool));
        assert_eq!(st.remove("foo"), Some(Type::Bool));
        assert_eq!(st.remove("foo"), None);
        assert_eq!(
            st.get("foo"),
            Err("Symbol `foo` not found in table".to_string())
        );
    }
}
