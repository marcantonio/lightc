use super::*;
use lex::Lex;

fn ast_to_string(ast: Result<&Ast<ast::Node>, &Vec<ParseError>>) -> String {
    match ast {
        Ok(ast) => ast.nodes().iter().map(|x| x.to_string()).collect(),
        Err(errs) => errs.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(" | "),
    }
}

macro_rules! run_insta {
    ($prefix:expr, $tests:expr) => {
        insta::with_settings!({ snapshot_path => "tests/snapshots", prepend_module_to_snapshot => false }, {
            for test in $tests {
                let tokens = Lex::new(test[1]).scan().expect("lexing failed in `parse` tests");
                let mut symbol_table = SymbolTable::new();
                let ast = Parse::new(&tokens, &mut symbol_table).parse().map(|(ast, ..)| ast);
                let ast_string = ast_to_string(ast.as_ref());
                insta::assert_yaml_snapshot!(format!("{}_{}", $prefix, test[0]), (test[1], ast, ast_string));
            }
        })
    };
}

#[test]
fn test_assignment() {
    let tests = [["basic", "x = x + 1"]];
    run_insta!("assignment", tests);
}

#[test]
fn test_binop() {
    let tests = [
        ["basic", "20 - 19"],
        ["invalid_op", "20 ! 19"],
        ["basic_var", "19 + a + 40"],
        ["bad_1", "20 -"],
        ["bad_2", "20 - else"],
        ["empty_paren", "()"],
        ["bad_3", "("],
        ["bad_4", "(19 + 21"],
        ["multi", "19 ** 21 ** 40; 19 - 21 * 20 + 40"],
        ["with_unop", "19 + 21 + -40"],
        ["single", "19"],
    ];
    run_insta!("binop", tests);
}

#[test]
fn test_block() {
    let tests = [
        ["basic", "if foo { bar }"],
        ["empty", "if foo {}"],
        ["missing", "if foo"],
        ["bad", "if foo {"],
        ["let", "let x: int = { 1 }"],
        ["multi", "y = { 1 + 4; foo(); 4 / 2 }"],
    ];
    run_insta!("block", tests);
}

#[test]
fn test_call() {
    let tests = [
        ["basic", "a(b, c)"],
        ["bad_1", "a("],
        ["bad_2", "a(a"],
        ["bad_3", "a(a,"],
        ["bad_4", "a(b b)"],
        ["nested", "a(b(c))"],
        ["nullary", "a()"],
        ["with_expr", "a(b + 1, c - 2 / 4)"],
    ];
    run_insta!("call", tests);
}

#[test]
fn test_char() {
    let tests = [["basic", "let c: char = 'a'"], ["control", "let nl: char = '\n'"]];
    run_insta!("char", tests);
}

#[test]
fn test_extern() {
    let tests = [["basic", "extern fn cos(x: float)"], ["err", "extern cos(x: float)"]];
    run_insta!("extern", tests);
}

#[test]
fn test_for() {
    let tests = [
        ["basic", "for x: int = 1; x < 10; 1 { foo }"],
        ["bad_1", "for"],
        ["bad_2", "for a"],
        ["bad_3", "for a:"],
        ["bad_4", "for a: int"],
        ["bad_5", "for a: int ="],
        ["bad_6", "for a: int = 1"],
    ];
    run_insta!("for", tests);
}

#[test]
fn test_func_def() {
    let tests = [
        [
            "basic",
            r#"
fn a(b: int, c: int) -> int {
    19 + a + 40
}
"#,
        ],
        [
            "multi_expr",
            r#"
fn a(b: int, c: int) -> int {
    19 + a + 40
    b + a
}
"#,
        ],
        [
            "no_ret_ty",
            r#"
fn a(b: int) {
    b
}
"#,
        ],
        ["empty", "fn a() {}"],
        [
            "multi_arg",
            r#"
fn (a: int, c: int) {
    1 + 2
}
"#,
        ],
        [
            "redefine_fn",
            r#"
fn foo() {}
fn bar() {}
fn foo() {}
"#,
        ],
        ["bad_1", "fn a(b: int) - { b }"],
        ["bad_2", "fn a(b: int) -> { b }"],
        ["bad_3", "fn a(b: int) -> not_a_type { b }"],
        ["bad_4", "fn a"],
        ["bad_5", "fn a( {}"],
        ["bad_6", "fn a(a: int, {}"],
        ["bad_7", "fn a(b: int b: int)"],
        ["bad_8", "fn a("],
        ["bad_9", "fn a(a: int, {}"],
        ["bad_10", "fn a(a: int"],
        ["bad_11", "fn a(a: int,"],
        ["bad_12", "fn a(b:)"],
        ["bad_13", "fn a(b)"],
    ];
    run_insta!("func_def", tests);
}

#[test]
fn test_gt_lt() {
    let tests = [["gt", "a + b > 40"], ["lt", "a < b / 40"]];
    run_insta!("gt_lt", tests);
}

#[test]
fn test_if() {
    let tests = [
        ["then", "if a > b { foo }"],
        [
            "else",
            r#"
if a > b {
    foo
} else {
    bar
}"#,
        ],
        [
            "then_else_if",
            r#"
if a > b {
    foo
} else if c < a {
    bar
}
"#,
        ],
        [
            "then_else_if_else",
            r#"
if a > b {
    foo
} else if c < a {
    bar
} else {
    baz
}
"#,
        ],
        ["bool_1", "if true { foo } else { bar }"],
        ["bool_2", "if false { foo } else { bar }"],
        ["bad", "if a > b { foo } else bar"],
    ];
    run_insta!("if", tests);
}

#[test]
fn test_let() {
    let tests = [
        ["basic", "let x: int = 1"],
        ["basic_float", "let x: float = 1.0"],
        ["bad_1", "let x: int ="],
        ["bad_2", "let x: int"],
        ["bad_3", "let x:"],
        ["bad_4", "let x"],
        ["bad_5", "let"],
    ];
    run_insta!("let", tests);
}

#[test]
fn test_logical_ops() {
    let tests = [
        ["eq", "x == 1"],
        ["and", "x && 1"],
        ["or", "x || 1"],
        ["complex", "x == 1 && y == 2 || z == 3"],
        ["complex_parens", "x == 1 && (y == 2 || z == 3)"],
    ];
    run_insta!("logical_ops", tests);
}

#[test]
fn test_op_prec() {
    let tests = [
        ["left_1", "19 + 21 * 40"],
        ["left_2", "19 * 21 - 40"],
        ["left_3", "19 - 21 + 40"],
        ["left_4", "19 - 21 * 20 + 40"],
        ["right_1", "19 ** 21 ** 40"],
        ["right_2", "19 ** 21 + 40"],
        ["right_3", "19 ** 21 ** 40 / 2"],
    ];
    run_insta!("op_prec", tests);
}

#[test]
fn test_parens() {
    let tests =
        [["excessive", "(((0)))"], ["prec", "(19 + 21) / 40"], ["complex", "3 * ((19 + 21) - 5) / 40"]];
    run_insta!("parens", tests);
}

#[test]
fn test_unop() {
    let tests = [
        ["basic", "-21"],
        ["with_binop", "-a * 2"],
        ["sub", "3 - -21"],
        ["right", "-4 ** 2"],
        ["double_neg_good", "-(-21)"],
        ["double_neg_bad", "--21"],
        ["invalid", "*2"],
    ];
    run_insta!("unop", tests);
}

#[test]
fn test_array() {
    let tests = [
        ["type", "let x: [int; 3]"],
        ["type_bad_1", "let x: [int;"],
        ["type_bad_2", "let x: [int"],
        ["type_bad_3", "let x: [int]"],
        ["type_bad_4", "let x: ["],
        ["type_bad_5", "let x: [foo]"],
        ["lit", "let x: [int; 3] = [1, 2, 3]"],
        ["empty_lit", "let x: [int; 3] = []"],
        ["index_1", "x[0]"],
        ["index_2", "x[1 + 2]"],
        ["index_3", "x[y[0]]"],
        ["index_bad_1", "x["],
        ["index_bad_2", "x[]"],
        ["index_bad_3", "x[0"],
        ["index_chain", "x[0][1]"],
    ];
    run_insta!("array", tests)
}

#[test]
fn test_struct() {
    let tests = [
        [
            "fields_only",
            r#"
struct Foo {
    let a: int
    let b: float = 1.0
}
"#,
        ],
        [
            "methods_only",
            r#"
struct Foo {
    fn c() -> int {
        1
    }
    fn d() {}
}
"#,
        ],
        [
            "mix",
            r#"
struct Foo {
    let a: int
    let b: float = 1.0

    fn c() -> int {
        1
    }
    fn d() {}
}
"#,
        ],
        [
            "dup",
            r#"
struct Foo {}
struct Foo {}
"#,
        ],
        ["field_selector", "x.y"],
        ["field_selector_bad", "x."],
        ["method_selector", "x.y(); x.y(a); x.y(a, b)"],
        ["method_selector_bad1", "x.y("],
        ["field_selector_bad2", "x.y(a"],
        ["field_selector_bad3", "x.y(a,"],
        ["field_selector_bad4", "x.y(a a"],
        [
            "selector_chaining",
            r#"
x.x.x
x().y()
x.y.z()
x.y().z
"#,
        ],
        ["empty", "struct Foo {}"],
        ["single_line_struct_with_field", "struct Foo { let x: int }"],
        ["single_line_struct_with_method", "struct Foo { fn foo() {} }"],
    ];
    run_insta!("struct", tests)
}

#[test]
fn test_error_recovery() {
    let tests = [
        [
            "basic",
            r#"
fn main() {
    le x: int = 1
    let y: int  2
}
"#,
        ],
        [
            "basic_struct",
            r#"
struct Foo {
    le a: int = 1
    let b: int 2
}
"#,
        ],
        [
            "find_open_brace",
            r#"
truct Foo {
    let a: int
    let b: flat
}
"#,
        ],
        [
            "fn_in_struct",
            r#"
struct Foo {
    let a: int
    let b float

    fn bang o: int) {
        printBang()
    }
}
"#,
        ],
        [
            "stmt_in_fn",
            r#"
fn bang(o: int) {
    printBang)
}
"#,
        ],
        /*
         * NOTE: it is redundant (at least for now) to test nested_for because a for
         * loop's inner blocks are parsed the same way a fn's inner blocks are. Included
         * for completeness and future-proofing.
         */
        [
            "nested_for",
            r#"
for i: int = 0; i <= ; 1 {
    for j: int  0; j <= 1; 1 {
        let x: int = i  j
    }
}
"#,
        ],
    ];
    run_insta!("recovery", tests)
}

#[test]
fn test_loop() {
    let tests = [
        ["basic", "loop { i += 1 }"],
    ];
    run_insta!("loop", tests);
}
