use serde::Serialize;
use std::fmt::Display;

use super::Prototype;
use crate::Node;
//use symbol_table::{symbol, Symbol};

#[derive(Debug, PartialEq, Clone, Serialize)]
pub struct For {
    pub start_name: String, // TODO: make this a Statement::Let
    pub start_antn: String,
    pub start_expr: Option<Box<Node>>,
    pub cond_expr: Box<Node>,
    pub step_expr: Box<Node>,
    pub body: Box<Node>,
}

impl Display for For {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = format!("(for ({}: {}", self.start_name, self.start_antn);
        if let Some(init) = &self.start_expr {
            s += &format!(" {}", init);
        }
        write!(f, "{}) {} {} {})", s, self.cond_expr, self.step_expr, self.body)
    }
}

#[derive(Debug, PartialEq, Clone, Serialize)]
pub struct Let {
    pub name: String,
    pub antn: String,
    pub init: Option<Box<Node>>,
}

impl Display for Let {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = format!("(let {}:{}", self.name, self.antn);
        if let Some(body) = &self.init {
            s += &format!(" {}", body);
        }
        write!(f, "{})", s)
    }
}

#[derive(Debug, PartialEq, Clone, Serialize)]
pub struct Fn {
    pub proto: Box<Prototype>,
    pub body: Option<Box<Node>>,
}

impl Display for Fn {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.body {
            Some(body) => write!(f, "(define {} {})", self.proto, body),
            _ => write!(f, "(define {})", self.proto),
        }
    }
}

#[derive(Debug, PartialEq, Clone, Serialize)]
pub struct Struct {
    pub name: String,
    pub fields: Vec<Node>,
    pub methods: Vec<Node>,
}

impl Display for Struct {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut attr_string = String::from("");
        attr_string += &self.fields.iter().fold(String::new(), |mut acc, n| {
            acc += &format!("{} ", n);
            acc
        });

        let mut meth_string = String::from("");
        meth_string += &self.methods.iter().fold(String::new(), |mut acc, n| {
            acc += &format!("{} ", n);
            acc
        });

        write!(
            f,
            "(struct {} '({}) '({}))",
            self.name,
            attr_string.strip_suffix(' ').unwrap_or(""),
            meth_string.strip_suffix(' ').unwrap_or("")
        )
    }
}

// // For new structs
// impl From<&Struct> for Symbol {
//     fn from(s: &Struct) -> Self {
//         let fields = s
//             .fields
//             .iter()
//             .map(|f| {
//                 let let_stmt = f.as_stmt().as_let();
//                 (let_stmt.name.to_owned(), let_stmt.antn.to_owned())
//             })
//             .collect();
//         Symbol {
//             name: s.name.to_owned(),
//             data: symbol::AssocData::Struct(symbol::StructData { fields, methods: None }),
//         }
//     }
// }
