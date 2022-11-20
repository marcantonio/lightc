use inkwell::values::PointerValue;
use std::collections::HashMap;

use crate::Codegen;
use common::symbol_table::{AssocData, Symbolic, VarData};
use common::{Symbol, SymbolTable, Type};

#[derive(PartialEq, Debug)]
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
        }
    }
}

impl<'a> From<(&str, &Type, PointerValue<'a>)> for CodegenSymbol<'a> {
    fn from((name, ty, ptr): (&str, &Type, PointerValue<'a>)) -> Self {
        CodegenSymbol {
            inner: Symbol { name: name.to_owned(), data: AssocData::Var(VarData { ty: ty.to_owned() }) },
            pointer: Some(ptr),
        }
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

impl<'ctx> Codegen<'ctx> {
    pub fn convert_table(mut old: SymbolTable<Symbol>) -> Result<SymbolTable<CodegenSymbol<'ctx>>, String> {
        let symbols = old.dump_table(0)?;
        let mut table = HashMap::with_capacity(symbols.len());
        // Filter takes advantage of a side-effect that will probably bite us. If the key
        // name doesn't match the symbol, it's because the symbol is from before the HIR
        // was constructed. Filtering them out is important since we now call
        // codegen_proto() on the symbol table.
        symbols.filter(|(name, sym)| name == &sym.name).for_each(|(k, v)| {
            table.insert(k, CodegenSymbol::from(v));
        });
        Ok(SymbolTable::with_table(table))
    }
}
