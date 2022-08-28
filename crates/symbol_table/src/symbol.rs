use common::Type;

#[derive(Clone, PartialEq, Debug)]
pub enum SymbolKind {
    Var,
    Fn { args: Vec<(String, Type)>, ret_ty: Type },
}

#[derive(Clone, PartialEq, Debug)]
pub struct Symbol {
    name: String,
    ty: Type,
    kind: SymbolKind,
}

impl Symbol {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn ty(&self) -> &Type {
        &self.ty
    }

    pub fn kind(&self) -> &SymbolKind {
        &self.kind
    }

    pub fn arg_tys(&self) -> Vec<&Type> {
        match &self.kind {
            SymbolKind::Fn { args, .. } => args.iter().map(|(_, ty)| ty).collect(),
            SymbolKind::Var => unreachable!("expected symbol to be a function"),
        }
    }

    pub fn ret_ty(&self) -> &Type {
        match &self.kind {
            SymbolKind::Fn { ret_ty, .. } => ret_ty,
            SymbolKind::Var => unreachable!("expected symbol to be a function"),
        }
    }
}

// For new functions
impl From<(&str, &[(String, Type)], &Type)> for Symbol {
    fn from((name, args, ret_ty): (&str, &[(String, Type)], &Type)) -> Self {
        Symbol {
            name: name.to_owned(),
            ty: Type::Void, // TODO: make fn type
            kind: SymbolKind::Fn { args: args.to_owned(), ret_ty: ret_ty.to_owned() },
        }
    }
}

// For new variables
impl From<(&str, &Type)> for Symbol {
    fn from((name, ty): (&str, &Type)) -> Self {
        Symbol { name: name.to_owned(), ty: ty.to_owned(), kind: SymbolKind::Var }
    }
}

impl From<&(String, Type)> for Symbol {
    fn from((name, ty): &(String, Type)) -> Self {
        Symbol { name: name.to_owned(), ty: ty.to_owned(), kind: SymbolKind::Var }
    }
}
