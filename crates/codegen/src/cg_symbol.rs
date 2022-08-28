use std::collections::HashMap;

use common::{Symbol, SymbolKind, SymbolTable, Symbolic, Type};
use inkwell::values::PointerValue;

use crate::Codegen;

#[derive(Clone, PartialEq, Debug)]
pub struct CgSymbol<'a> {
    name: String,
    ty: Type,
    kind: SymbolKind,
    pointer: Option<PointerValue<'a>>,
}

impl<'a> CgSymbol<'a> {
    pub fn pointer(&self) -> Option<PointerValue<'a>> {
        self.pointer
    }
}

impl<'a> Symbolic for CgSymbol<'a> {
    fn new_fn(name: &str, args: Vec<(String, Type)>, ret_ty: &Type) -> Self {
        CgSymbol {
            name: name.to_owned(),
            ty: Type::Void, // TODO: make fn type
            kind: SymbolKind::Fn { args, ret_ty: ret_ty.to_owned() },
            pointer: None,
        }
    }

    fn new_var(name: &str, ty: &Type) -> Self {
        CgSymbol { name: name.to_owned(), ty: ty.to_owned(), kind: SymbolKind::Var, pointer: None }
    }

    fn name(&self) -> &str {
        &self.name
    }

    fn ty(&self) -> &Type {
        &self.ty
    }

    fn kind(&self) -> &SymbolKind {
        &self.kind
    }

    fn arg_tys(&self) -> Vec<&Type> {
        match &self.kind {
            SymbolKind::Fn { args, .. } => args.iter().map(|(_, ty)| ty).collect(),
            SymbolKind::Var => unreachable!("expected symbol to be a function"),
        }
    }

    fn ret_ty(&self) -> &Type {
        match &self.kind {
            SymbolKind::Fn { ret_ty, .. } => ret_ty,
            SymbolKind::Var => unreachable!("expected symbol to be a function"),
        }
    }
}

impl<'a> From<(&str, &Type)> for CgSymbol<'a> {
    fn from((name, ty): (&str, &Type)) -> Self {
        CgSymbol::new_var(name, ty)
    }
}

impl<'a> From<(&str, &Type, PointerValue<'a>)> for CgSymbol<'a> {
    fn from((name, ty, ptr): (&str, &Type, PointerValue<'a>)) -> Self {
        CgSymbol { name: name.to_owned(), ty: ty.to_owned(), kind: SymbolKind::Var, pointer: Some(ptr) }
    }
}

impl<'a> From<Symbol> for CgSymbol<'a> {
    fn from(sym: Symbol) -> Self {
        let name = sym.name();
        let ty = sym.ty();
        match sym.kind() {
            SymbolKind::Fn { args, ret_ty } => CgSymbol::new_fn(name, args.to_vec(), ret_ty),
            SymbolKind::Var => CgSymbol::new_var(name, ty),
        }
    }
}

impl<'ctx> Codegen<'ctx> {
    pub fn convert_symbol_table(
        old_symbol_table: &SymbolTable<Symbol>,
    ) -> Result<SymbolTable<CgSymbol<'ctx>>, String> {
        let (keys, values) = old_symbol_table.dump_table(0)?;
        let mut table = HashMap::with_capacity(keys.len());
        keys.into_iter().zip(values).for_each(|(k, v)| {
            table.insert(k, CgSymbol::from(v));
        });
        Ok(SymbolTable::new_with_table(table))
    }
}
