use crate::Prototype;
use common::symbol_cache::AsSymbol;
use common::Type;

impl AsSymbol for Prototype {
    fn as_symbol(&self) -> String {
        let args = self.args().iter().fold(String::new(), |mut acc, (name, ty)| {
            acc += format!("{}:{}~", name, ty).as_str();
            acc
        });
        let ret_ty = format!("{}", self.ret_ty.as_ref().unwrap_or(&Type::Void)).to_ascii_lowercase();

        format!("{}~{}{}", self.name(), args, ret_ty)
    }
}

#[cfg(test)]
mod test {
    use crate::Prototype;
    use common::{symbol_cache::AsSymbol, Type};

    #[test]
    fn test_prototype() {
        use Type::*;

        let tests = [
            (
                Prototype {
                    name: String::from("foo"),
                    args: vec![(String::from("bar"), Int32)],
                    ret_ty: Some(Float),
                },
                "foo~bar:int32~float",
            ),
            (
                Prototype {
                    name: String::from("foo"),
                    args: vec![(String::from("bar"), Int32), (String::from("baz"), Int32)],
                    ret_ty: Some(Float),
                },
                "foo~bar:int32~baz:int32~float",
            ),
            (
                Prototype {
                    name: String::from("foo"),
                    args: vec![(String::from("bar"), Int32), (String::from("baz"), Int32)],
                    ret_ty: None,
                },
                "foo~bar:int32~baz:int32~void",
            ),
            (Prototype { name: String::from("foo"), args: vec![], ret_ty: Some(Float) }, "foo~float"),
        ];

        for test in tests {
            assert_eq!(test.0.as_symbol(), test.1)
        }
    }
}
