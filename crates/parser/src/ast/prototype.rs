use std::fmt::Display;

use serde::Serialize;

use symbol_table::Symbol;

#[derive(Debug, PartialEq, Clone, Serialize)]
pub struct Prototype {
    name: String,
    args: Vec<(String, String)>,
    ret_ty: Option<String>,
    is_extern: bool,
}

impl Prototype {
    pub fn new(
        name: String, args: Vec<(String, String)>, ret_ty: Option<String>, is_extern: bool,
    ) -> Prototype {
        Prototype { name, args, ret_ty, is_extern }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn set_name(&mut self, name: String) {
        self.name = name;
    }

    pub fn args(&self) -> &[(String, String)] {
        &self.args
    }

    pub fn set_args(&mut self, args: Vec<(String, String)>) {
        self.args = args;
    }

    pub fn ret_ty(&self) -> Option<&str> {
        self.ret_ty.as_deref()
    }

    pub fn set_ret_ty(&mut self, ret_ty: Option<String>) {
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
        let proto_name = if proto.name == "main" || proto.is_extern {
            proto.name.clone()
        } else {
            let args_string = args.iter().fold(String::new(), |mut acc, (_, ty)| {
                acc += format!("{}~", ty).as_str();
                acc
            });
            let ret_ty_string = proto.ret_ty.as_ref().unwrap_or(&String::from("void")).to_ascii_lowercase();
            format!("_{}~{}{}", proto.name, args_string, ret_ty_string)
        };

        Symbol::new_fn(
            proto_name.as_str(),
            args,
            proto.ret_ty.as_ref().unwrap_or(&String::from("void")),
            proto.is_extern,
        )
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
    use crate::ast::Prototype;
    use symbol_table::Symbol;

    #[test]
    fn test_prototype_to_symbol() {
        let tests = [
            (
                Prototype {
                    name: String::from("foo"),
                    args: vec![(String::from("bar"), String::from("int32"))],
                    ret_ty: Some(String::from("Float")),
                    is_extern: false,
                },
                "_foo~int32~float",
            ),
            (
                Prototype {
                    name: String::from("foo"),
                    args: vec![
                        (String::from("bar"), String::from("int32")),
                        (String::from("baz"), String::from("int32")),
                    ],
                    ret_ty: Some(String::from("Float")),
                    is_extern: false,
                },
                "_foo~int32~int32~float",
            ),
            (
                Prototype {
                    name: String::from("foo"),
                    args: vec![
                        (String::from("bar"), String::from("int32")),
                        (String::from("baz"), String::from("int32")),
                    ],
                    ret_ty: None,
                    is_extern: false,
                },
                "_foo~int32~int32~void",
            ),
            (
                Prototype {
                    name: String::from("foo"),
                    args: vec![],
                    ret_ty: Some(String::from("Float")),
                    is_extern: false,
                },
                "_foo~float",
            ),
        ];

        for test in tests {
            assert_eq!(test.1, Symbol::from(&test.0).name)
        }
    }
}
