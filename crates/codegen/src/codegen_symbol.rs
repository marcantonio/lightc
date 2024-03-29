use inkwell::values::PointerValue;
use std::collections::HashMap;
use std::fmt::Display;

use crate::Codegen;
use common::symbol_table::{AssocData, Symbolic};
use common::{Symbol, SymbolTable, Type};

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct CodegenSymbol<'a> {
    inner: Symbol,
    pointer: Option<PointerValue<'a>>,
}

impl<'a> CodegenSymbol<'a> {
    pub fn inner(&self) -> &Symbol {
        &self.inner
    }

    pub fn pointer(&self) -> Option<PointerValue<'a>> {
        self.pointer
    }

    pub fn new_var(name: &str, ty: &Type, module: &str, ptr: PointerValue<'a>) -> Self {
        Self { inner: Symbol::new_var(name, ty, module), pointer: Some(ptr) }
    }
}

impl<'a> Ord for CodegenSymbol<'a> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.inner.cmp(&other.inner)
    }
}

impl<'a> PartialOrd for CodegenSymbol<'a> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.inner.cmp(&other.inner))
    }
}

impl<'a> Symbolic for CodegenSymbol<'a> {
    fn name(&self) -> &str {
        self.inner.name()
    }

    fn kind(&self) -> &str {
        match self.inner.data {
            AssocData::Fn(_) => "Fn",
            AssocData::Var(_) => "Var",
            AssocData::Struct(_) => "Struct",
            AssocData::Module(_) => "Module",
        }
    }

    fn is_exportable(&self) -> bool {
        self.inner.is_exportable
    }
}

impl<'a> From<Symbol> for CodegenSymbol<'a> {
    fn from(sym: Symbol) -> Self {
        CodegenSymbol { inner: sym, pointer: None }
    }
}

// impl<'a> From<&CodegenSymbol<'a>> for Prototype {
//     fn from(sym: &CodegenSymbol) -> Self {
//         let sym = &sym.inner;
//         Prototype::new(
//             sym.name().to_owned(),
//             sym.args()
//                 .iter()
//                 .map(|(n, ty)| ((*n).to_owned(), (*ty).to_owned()))
//                 .collect::<Vec<(String, Type)>>(),
//             sym.ret_ty().to_owned(),
//             sym.is_extern(),
//         )
//     }
// }

impl<'a> Display for CodegenSymbol<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.inner())
    }
}

impl<'ctx> Codegen<'ctx> {
    pub fn convert_table(mut old: SymbolTable<Symbol>) -> Result<SymbolTable<CodegenSymbol<'ctx>>, String> {
        let symbols = old.dump_table(0)?;
        let mut table = HashMap::with_capacity(symbols.len());
        // Filter takes advantage of a side-effect that will probably bite us. If the key
        // name doesn't match the symbol, it's because the symbol is from before the HIR
        // was constructed. Filtering them out is important since we now call
        // codegen_proto() on the symbol table.
        symbols.into_iter().filter(|(name, sym)| name == &sym.name).for_each(|(k, v)| {
            table.insert(k, CodegenSymbol::from(v));
        });
        Ok(SymbolTable::with_table(table))
    }
}
