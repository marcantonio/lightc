use super::*;
use lex::Lex;
use parse::Parse;
use tych::Tych;

macro_rules! run_insta {
    ($prefix:expr, $tests:expr) => {
        insta::with_settings!({ snapshot_path => "tests/snapshots", prepend_module_to_snapshot => false }, {
            for test in $tests {
                let tokens = Lex::new(test[1]).scan().expect("lexing faled in `lower` tests");
                let (ast, mut symbol_table, _, _) = Parse::new(&tokens).parse().expect("parsing failed in `lower` tests");
                let typed_ast = Tych::new(&mut symbol_table).walk(ast).expect("type checking failed in `lower` tests");
                let res = Lower::new(vec![], &mut symbol_table).walk(typed_ast);
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
fn test_struct() {
    let tests = [
        [
            "selector",
            r#"
fn returnStruct() -> Foo {
    let a: Foo
    a
}
fn main() {
    let x: Foo
    x.a
    returnStruct().a
    let b: Bar
    b.foo.b()
    b.foo.a
}
struct Foo {
    let a: int
    fn b() {}
}
struct Bar {
    let foo: Foo
}
"#,
        ],
        [
            "self",
            r#"
struct Foo {
    let a: int
    fn b() -> int { self.a + 1 }
}
"#,
        ],
    ];
    run_insta!("struct", tests);
}

#[test]
fn test_init_literal() {
    let tests = [
        [
            "basic",
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
        ],
        [
            "struct",
            r#"
fn main() {
    let x: Foo
}
struct Foo {
    let a: int
    let b: bool
}
"#,
        ],
        [
            "nested_struct",
            r#"
fn main() {
    let x: Foo
}
struct Foo {
    let a: int
    let b: bool
}
struct Bar {
    let a: Foo
}
"#,
        ],
    ];
    run_insta!("init_literal", tests);
}
