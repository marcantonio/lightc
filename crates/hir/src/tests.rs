use lexer::Lexer;
use parser::Parser;

use super::*;

macro_rules! run_insta {
    ($prefix:expr, $tests:expr) => {
        insta::with_settings!({ snapshot_path => "tests/snapshots", prepend_module_to_snapshot => false }, {
            for test in $tests {
                let tokens = Lexer::new(test[1]).scan().unwrap();
                let mut symbol_table = SymbolTable::new();
                let ast = Parser::new(&tokens, &mut symbol_table).parse().unwrap();
                let res = Hir::new(&mut symbol_table).walk(ast);
                insta::assert_yaml_snapshot!(format!("{}_{}", $prefix, test[0]), (test[1], res));
            }
        })
    };
}

#[test]
fn test_binop() {
    let tests = [[
        "all",
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
    ]];
    run_insta!("binop", tests);
}

#[test]
fn test_redefine_fn() {
    let tests = [[
        "basic",
        r#"
fn foo() {}
fn bar() {}
fn foo() {}
"#,
    ]];
    run_insta!("redefined_fn", tests);
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
