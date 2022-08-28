use inkwell::values::PointerValue;
use std::collections::HashMap;

use common::Type;
use symbol_table::{Symbol, SymbolKind, SymbolTable};

use crate::Codegen;

#[derive(PartialEq, Debug)]
pub struct CodegenSymbol<'a> {
    name: String,
    ty: Type,
    kind: SymbolKind,
    pointer: Option<PointerValue<'a>>,
}

impl<'a> CodegenSymbol<'a> {
    pub fn pointer(&self) -> Option<PointerValue<'a>> {
        self.pointer
    }
}

impl<'a> From<(&str, &Type, PointerValue<'a>)> for CodegenSymbol<'a> {
    fn from((name, ty, ptr): (&str, &Type, PointerValue<'a>)) -> Self {
        CodegenSymbol { name: name.to_owned(), ty: ty.to_owned(), kind: SymbolKind::Var, pointer: Some(ptr) }
    }
}

impl<'a> From<Symbol> for CodegenSymbol<'a> {
    fn from(sym: Symbol) -> Self {
        let name = sym.name();
        let ty = sym.ty();
        match sym.kind() {
            SymbolKind::Fn { args, ret_ty } => CodegenSymbol {
                name: name.to_owned(),
                ty: Type::Void,
                kind: SymbolKind::Fn { args: args.to_owned(), ret_ty: ret_ty.to_owned() },
                pointer: None,
            },
            SymbolKind::Var => CodegenSymbol {
                name: name.to_owned(),
                ty: ty.to_owned(),
                kind: SymbolKind::Var,
                pointer: None,
            },
        }
    }
}

impl<'ctx> Codegen<'ctx> {
    pub fn convert_table(mut old: SymbolTable<Symbol>) -> Result<SymbolTable<CodegenSymbol<'ctx>>, String> {
        let symbols = old.dump_table(0)?;
        let mut table = HashMap::with_capacity(symbols.len());
        symbols.for_each(|(k, v)| {
            table.insert(k, CodegenSymbol::from(v));
        });
        Ok(SymbolTable::with_table(table))
    }
}
