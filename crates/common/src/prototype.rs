use serde::Serialize;
use std::fmt::Display;

use crate::{Symbol, Type};

#[derive(Debug, PartialEq, Eq, Clone, Serialize)]
pub struct Prototype {
    name: String,
    args: Vec<(String, Type)>,
    ret_ty: Type,
    is_extern: bool,
    module: String,
}

impl Prototype {
    pub fn new(
        name: String, args: Vec<(String, Type)>, ret_ty: Type, is_extern: bool, is_method: bool,
        module: String,
    ) -> Prototype {
        // Prepend the local module name for local functions
        let name =
            if is_extern || is_method || name == "main" { name } else { format!("{}::{}", module, name) };
        Prototype { name, args, ret_ty, is_extern, module }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn set_name(&mut self, name: String) {
        self.name = name;
    }

    pub fn args(&self) -> &[(String, Type)] {
        &self.args
    }

    pub fn set_args(&mut self, args: Vec<(String, Type)>) {
        self.args = args;
    }

    pub fn ret_ty(&self) -> &Type {
        &self.ret_ty
    }

    pub fn set_ret_ty(&mut self, ret_ty: Type) {
        self.ret_ty = ret_ty;
    }

    pub fn is_extern(&self) -> bool {
        self.is_extern
    }
}

impl From<&Prototype> for Symbol {
    fn from(proto: &Prototype) -> Self {
        let args = proto.args.as_slice();

        // Don't mangle the name for main and externs
        let cooked_name = if proto.name == "main" || proto.is_extern {
            proto.name.clone()
        } else {
            let args_string = args.iter().fold(String::new(), |mut acc, (_, ty)| {
                acc += format!("{}~", ty).as_str();
                acc
            });
            let new_name = format!("{}~{}{}", proto.name, args_string, proto.ret_ty);

            // One underscore is enough
            if new_name.starts_with('_') {
                new_name
            } else {
                format!("_{}", new_name)
            }
        };

        Symbol::new_fn(&cooked_name, &proto.name, args, &proto.ret_ty, proto.is_extern, &proto.module, true)
    }
}

impl From<Symbol> for Prototype {
    fn from(sym: Symbol) -> Self {
        let sym_name_parts = sym
            .name
            .split_once("::")
            .unwrap_or_else(|| unreachable!("couldn't split module name in `from()`"));
        let module = &sym_name_parts.0[1..];
        let args = sym.args().iter().cloned().map(|(n, t)| (n.to_owned(), t.clone())).collect();

        Prototype {
            name: sym.name.to_owned(),
            args,
            ret_ty: sym.ret_ty().to_owned(),
            is_extern: sym.is_extern(),
            module: module.to_owned(),
        }
    }
}

impl Display for Prototype {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = format!("({}", self.name);
        if !self.args.is_empty() {
            for arg in &self.args {
                s += &format!(" {}:{}", arg.0, arg.1);
            }
        }
        write!(f, "{})", s)
    }
}

#[cfg(test)]
mod test {
    use crate::{Symbol, Type};

    use super::Prototype;

    #[test]
    fn test_prototype_to_symbol() {
        let tests = [
            (
                Prototype::new(
                    String::from("foo"),
                    vec![(String::from("bar"), Type::Int32)],
                    Type::Float,
                    false,
                    false,
                    String::from("main"),
                ),
                "_main::foo~int32~float",
            ),
            (
                Prototype::new(
                    String::from("foo"),
                    vec![(String::from("bar"), Type::Int32), (String::from("baz"), Type::Int32)],
                    Type::Float,
                    false,
                    false,
                    String::from("main"),
                ),
                "_main::foo~int32~int32~float",
            ),
            (
                Prototype::new(
                    String::from("foo"),
                    vec![(String::from("bar"), Type::Int32), (String::from("baz"), Type::Int32)],
                    Type::Void,
                    false,
                    false,
                    String::from("main"),
                ),
                "_main::foo~int32~int32~void",
            ),
            (
                Prototype::new(String::from("foo"), vec![], Type::Float, false, false, String::from("main")),
                "_main::foo~float",
            ),
        ];

        for test in tests {
            assert_eq!(test.1, Symbol::from(&test.0).name)
        }
    }
}
