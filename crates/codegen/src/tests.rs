use super::*;
use lex::Lex;
use lower::Lower;
use parse::Parse;
use tych::Tych;

macro_rules! run_insta {
    ($prefix:expr, $tests:expr) => {
        insta::with_settings!({ snapshot_path => "tests/snapshots", prepend_module_to_snapshot => false }, {
            for test in $tests {
                // Unoptimized code
                let tokens = Lex::new(test[1]).scan().expect("lexing failed in `codegen` tests");
                let mut symbol_table = SymbolTable::new();
                let (ast, _, _) = Parse::new(&tokens, &mut symbol_table).parse().expect("parsing failed in `codegen` tests");
                let typed_ast = Tych::new("main", &mut symbol_table).walk(ast).expect("type checking failed in `codegen` tests");
                let hir = Lower::new("main", &mut symbol_table).walk(typed_ast).expect("lowering failed in `codegen` tests");
                let args = CliArgs::new();
                let res = Codegen::run(hir, "main", symbol_table, PathBuf::new(), &args, true)
                    .expect("codegen error").to_ir_string();

                // Optimized code
                let tokens = Lex::new(test[1]).scan().expect("lexing faled in `codegen` tests");
                let mut symbol_table = SymbolTable::new();
                let (ast, _, _) = Parse::new(&tokens, &mut symbol_table).parse().expect("parsing failed in `codegen` tests");
                let typed_ast = Tych::new("main", &mut symbol_table).walk(ast).expect("type checking failed in `codegen` tests");
                let hir = Lower::new("main", &mut symbol_table).walk(typed_ast).expect("lowering failed in `codegen` tests");
                let mut args = CliArgs::new();
                args.opt_level = 1;
                let res_opt = Codegen::run(hir, "main", symbol_table, PathBuf::new(), &args, true)
                    .expect("codegen error").to_ir_string();

                insta::assert_yaml_snapshot!(format!("{}_{}", $prefix, test[0]), (test[1], res, res_opt));
            }
        })
    };
}

#[test]
fn test_block() {
    let tests = [[
        "basic",
        r#"
fn main() {
    {
        10 + 2
        1.0
        5
    }
}
"#,
    ]];
    run_insta!("block", tests);
}

#[test]
fn test_for() {
    let tests = [[
        "basic",
        r#"
extern fn putchar(x: int) -> int
fn main() {
    let x: int = 3
    for y: int = 0; y < x; 1 {
        putchar(46)
    }
    putchar(10)
}
"#,
    ]];
    run_insta!("for", tests);
}

#[test]
fn test_cond() {
    let tests = [
        [
            "cond_success",
            r#"
fn plus_one(x: int) -> int { x + 1 }
fn main() {
    if plus_one(6) == 7 {
        7
    }
}
"#,
        ],
        [
            "cond_fail",
            r#"
fn plus_one(x: int) -> int { x + 1 }
fn main() {
    if plus_one(6) == 5 {
        7
    }
}
"#,
        ],
        [
            "if_else_cond_success",
            r#"
fn plus_one(x: int) -> int { x + 1 }
fn main() {
    if plus_one(6) == 7 {
        7
    } else {
        1
    }
}
"#,
        ],
        [
            "if_else_cond_fail",
            r#"
fn plus_one(x: int) -> int { x + 1 }
fn main() {
    if plus_one(6) == 8 {
        7
    } else {
        1
    }
}
"#,
        ],
        [
            "if_else_if_else_cond_success",
            r#"
fn plus_one(x: int) -> int { x + 1 }
fn main() {
    if plus_one(6) == 7 {
        7
    } else if plus_one(1) == 2 {
        2
    } else {
        1
    }
}
"#,
        ],
        [
            "if_else_if_else_cond_2_success",
            r#"
fn plus_one(x: int) -> int { x + 1 }
fn main() {
    if plus_one(6) == 5 {
        7
    } else if plus_one(1) == 2 {
        2
    } else {
        1
    }
}
"#,
        ],
        [
            "if_else_if_else_conds_fail",
            r#"
fn plus_one(x: int) -> int { x + 1 }
fn main() {
    if plus_one(6) == 5 {
        7
    } else if plus_one(1) == 3 {
        2
    } else {
        1
    }
}
"#,
        ],
        [
            "if_else_if_cond_success",
            r#"
fn plus_one(x: int) -> int { x + 1 }
fn main() {
    if plus_one(6) == 7 {
        7
    } else if plus_one(1) == 1 {
        2
    }
}
"#,
        ],
        [
            "if_else_if_cond_2_success",
            r#"
fn plus_one(x: int) -> int { x + 1 }
fn main() {
    if plus_one(6) == 5 {
        7
    } else if plus_one(1) == 2 {
        2
    }
}
"#,
        ],
        [
            "true_lit",
            r#"
fn main() {
    if true {
        7
    } else {
        2
    }
}
"#,
        ],
        [
            "false_lit",
            r#"
fn main() {
    if false {
        7
    } else {
        2
    }
}
"#,
        ],
    ];
    run_insta!("cond", tests);
}

#[test]
fn test_let() {
    let tests = [
        [
            "basic",
            r#"
        fn main() {
    let x: int = 1
}
"#,
        ],
        [
            "float_default",
            r#"
fn main() {
    let x: float
}
"#,
        ],
        [
            "bool",
            r#"
fn main() {
    let x: bool
}
"#,
        ],
    ];
    run_insta!("let", tests);
}

#[test]
fn test_scope() {
    let tests = [
        [
            "basic_shadowing",
            r#"
fn foo(a: int) -> int {
    let b: int = 1
    {
        let b: bool = false
    }
    b
}
fn main() { foo(3) }
"#,
        ],
        [
            "nested_shadowing",
            r#"
fn foo(a: int) -> int {
    let b: int = 1
    {
        let b: bool = false
        let a: float = {
            let b: float = 1.0
            b
        }
    }
    b
}
fn main() { foo(3) }
"#,
        ],
        [
            "for",
            r#"
fn foo() {
    let x: float = 1.0
    for x: int = 1; x < 10; 1 {
        x
    }
    x
}
fn main() { foo() }
"#,
        ],
        [
            "if",
            r#"
fn foo() {
    let x: float = 1.0
    if x < 2.0 {
        let y: int = 2
        x
    }
    x
}
fn main() { foo() }
"#,
        ],
        [
            "if_else",
            r#"
fn foo() {
    let x: float = 1.0
    if x < 2.0 {
        let y: int = 4 & 3 ^ 1
        y
    } else {
        let y: int = -2
        y
    }
}
fn main() { foo() }
"#,
        ],
    ];
    run_insta!("scope", tests);
}

#[test]
fn test_unop() {
    let tests = [[
        "basic",
        r#"
fn test(x: int) -> int {
    x + 1
}

fn main() {
    test(-40)
}
"#,
    ]];
    run_insta!("unop", tests);
}

#[test]
fn test_array() {
    let tests = [[
        "basic",
        r#"
fn main() {
    let a: [int; 3] = [1, 2, 3]
    let b: [int; 3]
    a[1] = 7
    a[1]
}
"#,
    ]];
    run_insta!("array", tests);
}

#[test]
fn test_order() {
    let tests = [
        [
            "a",
            r#"
fn foo() {}
fn main() {
    foo()
}
"#,
        ],
        [
            "b",
            r#"
fn main() {
    foo()
}
fn foo() {}
"#,
        ],
    ];
    run_insta!("order", tests);
}

#[test]
fn test_struct() {
    let tests = [
        [
            "basic",
            r#"
struct Foo {
    let a: int
    let b: bool
    fn c(d: int) -> int { self.a + d }
}
fn main() {
    let x: Foo
    x.a
    x.c(2)
}
"#,
        ],
        [
            "selector",
            r#"
fn returnStruct() -> Foo {
    let a: Foo
    a.a = 1
    a
}
fn main() {
    let x: Foo
    x.a
    let b: Bar
    b.foo.a = returnStruct().a
    b.foo.b()
    b.foo.a
    b.d(2)
}
struct Foo {
    let a: int
    fn b() {}
}
struct Bar {
    let foo: Foo
    let c: [int; 3]
    fn d(i: int) -> int { self.c[i] }
}
"#,
        ],
        [
            "self",
            r#"
struct Foo {
    let a: int
    let b: [int; 5]
    fn init(a: int) {
        self.a = a
    }
    fn bar() {
        self.b[self.a]
    }
}
fn main() {
    let foo: Foo
    foo.init(2)
    foo.a
}
"#,
        ],
    ];
    run_insta!("struct", tests);
}

#[test]
fn test_loop() {
    let tests = [
        [
            "basic",
            r#"
fn main() {
    let i: int = 0
    loop {
        i += 1
    }
}
"#,
        ],
        [
            "if_breaks",
            r#"
fn main() {
    let i: int = 0
    loop {
        if i == 0 {
            break
        } else {
            break
        }
        i += 1
    }
    i += 1
}
"#,
        ],
        [
            "if_expr",
            r#"
fn main() {
    let i: int = 0
    loop {
        i += 1
        if i == 1 {
            2
        } else {
            3
        }
    }
    i += 1
}
"#,
        ],
        [
            "both",
            r#"
fn main() {
    let i: int = 0
    loop {
        if i == 0 {
            break
        } else {
            break
        }
        i += 1
        if i == 1 {
            2
        } else {
            3
        }
        i += 1
    }
    i += 1
}
"#,
        ],
        [
            "end_break",
            r#"
fn main() {
    let i: int = 0
    loop {
        i += 1
        break
    }
    i += 1
}
"#,
        ],
        [
            "with_for",
            r#"
fn main() {
    let i: int = 0
    loop {
        if i == 0 {
            break
        } else {
            for i: int; i < 2; 1 {
                i += 1
            }
        }
        i += 1
    }
    i += 1
}
"#,
        ],
        [
            "cond_break",
            r#"
fn main() {
    let i: int = 0
    loop {
        i += 1
        if i == 1 {
            2
        } else {
            3
        }
        if true {
            break
        }
        i += 1
    }
    i += 1
}
"#,
        ],
        [
            "nested_breaks",
            r#"
fn main() {
    let i: int = 0
    loop {
        i += 1
        loop {
            i += 1
            break
        }
        i += 1
        break
    }
    i += 1
}
"#,
        ],
        [
            "next",
            r#"
fn main() {
    let i: int = 0
    loop {
        i += 1
        if i == 1 {
            next
        }
    }
    i += 1
}
"#,
        ],
        [
            "nested_next",
            r#"
fn main() {
    let i: int = 0
    loop {
        i += 1
        loop {
            if i == 1 {
                next
            }
        }
        next
    }
    i += 1
}
"#,
        ],

    ];
    run_insta!("loop", tests);
}
