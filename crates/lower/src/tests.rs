use super::*;
use lex::Lex;
use parse::Parse;
use tych::Tych;

macro_rules! run_insta {
    ($prefix:expr, $tests:expr) => {
        insta::with_settings!({ snapshot_path => "tests/snapshots", prepend_module_to_snapshot => false }, {
            for test in $tests {
                let tokens = Lex::new(test[1]).scan().unwrap();
                let mut symbol_table = SymbolTable::new();
                let ast = Parse::new(&tokens, &mut symbol_table).parse().unwrap();
                let tyst = Tych::new(&mut symbol_table).walk(ast).unwrap();
                let res = Lower::new(&mut symbol_table).walk(tyst);
                insta::assert_yaml_snapshot!(format!("{}_{}", $prefix, test[0]), (test[1], res));
            }
        })
    };
}

#[test]
fn test_binop() {
    let tests = [
        [
            "all_ops",
            r#"
fn main() {
    let y: int
    y += 1
    y -= 1
    y *= 1
    y /= 1
    y <= 1
}
"#,
        ],
        [
            "inner",
            r#"
fn main() {
    let x: int = 1
    let y: bool = x <= 3
}
"#,
        ],
    ];
    run_insta!("binop", tests);
}

#[test]
fn test_func_call() {
    let tests = [
        [
            "def_first",
            r#"
fn foo() {}

fn main() {
    foo()
}
"#,
        ],
        [
            "def_second",
            r#"
fn main() {
    foo()
}

fn foo() {}
"#,
        ],
        [
            "mix1",
            r#"
fn main() {
    foo()
}

fn foo() {}

fn bar() {
    foo()
}
"#,
        ],
        [
            "mix2",
            r#"
fn main() {
    foo()
    foo()
}

fn foo() {}

fn bar() {
    foo()
}
"#,
        ],
        [
            "mix3",
            r#"
fn main() {
    foo()
}

fn foo() {}

fn bar() {
    foo()
    foo()
}
"#,
        ],
        [
            "recursive",
            r#"
fn foo() {
    foo()
}

fn main() {
    foo()
}
"#,
        ],
    ];
    run_insta!("func_call", tests);
}

#[test]
fn test_init_literal() {
    let tests = [[
        "all",
        r#"
fn main() {
    let x: int
    let x: int8
    let x: int16
    let x: int32
    let x: int64
    let x: uint
    let x: uint8
    let x: uint16
    let x: uint32
    let x: uint64
    let x: float
    let x: double
    let x: char
    let x: bool
    let x: [bool; 3]
}
"#,
    ]];
    run_insta!("init_literal", tests);
}
