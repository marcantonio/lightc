use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct SymbolCache {
    symbols: HashMap<String, bool>, // XXX &str
}

impl SymbolCache {
    pub fn new() -> Self {
        SymbolCache { symbols: HashMap::new() }
    }

    pub fn insert(&mut self, sym: &dyn AsSymbol) {
        self.symbols.insert(sym.as_symbol(), true);
    }

    pub fn exists(&self, sym: &str) -> bool {
        self.symbols.contains_key(sym)
    }
}

impl Default for SymbolCache {
    fn default() -> Self {
        Self::new()
    }
}

pub trait AsSymbol {
    fn as_symbol(&self) -> String;
}
