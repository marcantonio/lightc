use super::*;
use lexer::Lexer;
use parser::Parser;
use type_checker::TypeChecker;

macro_rules! run_insta {
    ($prefix:expr, $tests:expr) => {
        insta::with_settings!({ snapshot_path => "tests/snapshots", prepend_module_to_snapshot => false }, {
            for test in $tests {
                let tokens = Lexer::new(test[1]).scan().unwrap();
                let mut symbol_table = SymbolTable::new();
                let ast = Parser::new(&tokens, &mut symbol_table).parse().unwrap();
                let tyst = TypeChecker::new(&mut symbol_table).walk(ast).unwrap();
                let res = Hir::new(&mut symbol_table).walk(tyst);
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
