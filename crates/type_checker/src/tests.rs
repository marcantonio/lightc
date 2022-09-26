use lexer::Lexer;
use parser::Parser;

use super::*;

const ERR_STR: &str = "Numeric literal out of range";

macro_rules! run_insta {
    ($prefix:expr, $tests:expr) => {
        insta::with_settings!({ snapshot_path => "tests/snapshots", prepend_module_to_snapshot => false }, {
            for test in $tests {
                let tokens = Lexer::new(test[1]).scan().unwrap();
                let mut symbol_table = SymbolTable::new();
                let ast = Parser::new(&tokens, &mut symbol_table).parse().unwrap();
                let res = TypeChecker::new(&mut symbol_table).walk(ast);
                insta::assert_yaml_snapshot!(format!("{}_{}", $prefix, test[0]), (test[1], res));
            }
        })
    };
}

#[test]
fn test_binop() {
    let tests = [
        [
            "basic",
            r#"
fn foo() {
    1 + 2
}
"#,
        ],
        [
            "basic_var",
            r#"
fn foo() {
    let a: int = 1
    a + 2
}
"#,
        ],
        [
            "complex",
            r#"
fn foo() {
    let a: int = 1
    a + 2 / 4 + (2 * 2)
}
"#,
        ],
        [
            "func_call",
            r#"
fn plusOne(x: int) -> int {
    x + 1
}

fn main() {
    1 + plusOne(3)
}
"#,
        ],
        [
            "mismatch",
            r#"
fn foo() {
    2.0 + 1
}
"#,
        ],
        [
            "bool_ret",
            r#"
fn foo() -> bool {
    2 == 1
}
"#,
        ],
        [
            "bad_lhs_assign",
            r#"
fn main(x: int) {
    x + 1 = 1
}
"#,
        ],
        [
            "bools_cmp_1",
            r#"
fn main(x: int) {
    true || false
}
"#,
        ],
        [
            "bools_cmp_2",
            r#"
fn main(x: bool) {
    x == false
}
"#,
        ],
        [
            "bad_lit_int",
            r#"
fn main(x: int) {
    true && 1
}
"#,
        ],
        [
            "bad_lit_float",
            r#"
fn main(x: int) {
    1.0 || true
}
"#,
        ],
        [
            "bad_cmp_type",
            r#"
fn main(x: int) {
    true > true
}
"#,
        ],
        [
            "bad_math_types",
            r#"
fn main(x: int) {
    true + false
}
"#,
        ],
        [
            "lit_char_1",
            r#"
fn main(x: int) {
    'a' > 'c'
}
"#,
        ],
        [
            "lit_char_2",
            r#"
fn main(x: char) {
    x > 'c'
}
"#,
        ],
    ];
    run_insta!("binop", tests);
}

#[test]
fn test_block() {
    let tests = [
        [
            "let",
            r#"
let x: int = {
    1
}
"#,
        ],
        [
            "let_mismatch_1",
            r#"
let x: int = {
    1.0
}
"#,
        ],
        [
            "let_mismatch_2",
            r#"
fn foo() {
    let x: int = {
        11.0
        foo()
    }
}
"#,
        ],
    ];
    run_insta!("block", tests);
}

#[test]
fn test_call() {
    let tests = [
        [
            "basic",
            r#"
fn plusOne(x: int) -> int {
    x + 1
}
fn main() {
    plusOne(1)
}
"#,
        ],
        [
            "mismatch_arg_type",
            r#"
fn plusOne(x: int) -> int {
    x + 1
}
fn main() {
    let x: float = 1.0
    plusOne(x)
}
"#,
        ],
        [
            "mismatch_arg_num",
            r#"
fn plusOne(x: int) -> int {
    x + 1
}
fn main() {
    plusOne(1, 2)
}
"#,
        ],
        [
            "undef_func",
            r#"
fn plusOne(x: int) -> int {
    x + 1
}
fn main() {
    plusThree(1)
}
"#,
        ],
    ];
    run_insta!("call", tests);
}

#[test]
fn test_cond() {
    let tests = [
        [
            "basic",
            r#"
fn foo() {
    if 1 > 2 {
        1
    } else {
        2
    }
}
"#,
        ],
        [
            "bad_cond_1",
            r#"
fn foo() {
    let x: int8 = 1
    let y: int16 = 2
    if x < y {
        1
    }
}
"#,
        ],
        [
            "bad_cond_2",
            r#"
fn foo() {
    if 1.0 {
        1
    }
}
"#,
        ],
        [
            "mismatch_arms",
            r#"
fn foo() {
    if 1 > 2 {
        1
    } else {
        2.0
    }
}
"#,
        ],
    ];
    run_insta!("cond", tests);
}

#[test]
fn test_def_func() {
    let tests = [
        [
            "basic",
            r#"
fn foo() {
    1
}
"#,
        ],
        [
            "void_ret_void_body",
            r#"
fn bar() { }
fn foo() {
    bar()
}
"#,
        ],
        [
            "void_ret_expr_body",
            r#"
fn foo(a: int) {
    a + 1
}
"#,
        ],
        [
            "multi_args",
            r#"
fn foo(a: int, b: float) { }
"#,
        ],
        [
            "expected_int_last_stmt_1",
            r#"
fn foo(a: int, b: float) -> int { }
"#,
        ],
        [
            "expected_int_last_stmt_2",
            r#"
fn foo(a: int, b: float) -> int {
    1.0
}
"#,
        ],
        [
            "extern",
            r#"
extern fn foo()
"#,
        ],
        [
            "stmt_end_of_body",
            r#"
fn foo() {
    let a: int8 = 1
}
"#,
        ],
        [
            "main_void",
            r#"
fn main() { }
"#,
        ],
        [
            "main_antn",
            r#"
fn main() -> int { }
"#,
        ],
    ];
    run_insta!("def_func", tests);
}

#[test]
fn test_for() {
    let tests = [
        [
            "basic",
            r#"
fn foo() {
    for x: int8 = 1; x < 2; 1 {
        x
    }
}
"#,
        ],
        [
            "for_shadowing1",
            r#"
fn foo() {
    let x: int32 = 1
    for x: int8 = 1; x < 2; 1 {
        x
    }
    x
}
"#,
        ],
        [
            "for_shadowing2",
            r#"
fn foo() {
    let x: [int32; 3] = [1, 2, 3]
    x[0]
    for x: int8 = 1; x < 2; 1 {
        x
    }
    x[0]
}
"#,
        ],
        [
            "for_shadowing3",
            r#"
fn foo() -> float {
    let x: float = 1.0
    for x: int8 = 1; x < 2; 1 {
        x
    }
    x
}
"#,
        ],
        [
            "antn_mismatch_1",
            r#"
fn foo() {
    for x: int8 = 1.0; x < 2; 1 {
        x
    }
}
"#,
        ],
        [
            "antn_mismatch_2",
            r#"
fn foo() {
    let y: int8 = 2
    for x: int = y; x < 2; 1 {
        x
    }
}
"#,
        ],
        [
            "cond_should_bool",
            r#"
fn foo() {
    for x: int = 1; 2.0; 1 {
        x
    }
}
"#,
        ],
        [
            "lit_step_mismatch",
            r#"
fn foo() {
    for x: int = 1; x < 3; 1.0 {
        x
    }
}
"#,
        ],
        [
            "var_step_mismatch",
            r#"
fn foo() {
    let y: int8 = 2
    for x: int = 1; x < 3; y {
        x
    }
}
"#,
        ],
    ];
    run_insta!("for", tests);
}

#[test]
fn test_ident() {
    let tests = [
        [
            "basic",
            r#"
fn foo(x: int) { x }
"#,
        ],
        [
            "unknown_var",
            r#"
fn foo(x: int) { y }
"#,
        ],
    ];
    run_insta!("ident", tests);
}

#[test]
fn test_let() {
    let tests = [
        [
            "basic",
            r#"
fn foo() {
    let x: int = 3
}
"#,
        ],
        [
            "basic_no_init",
            r#"
        fn foo() {
            let x: int
        }
        "#,
        ],
        [
            "lit_antn_mismatch",
            r#"
fn foo() {
    let x: int = 3.0
}
"#,
        ],
        [
            "var_antn_mismatch",
            r#"
fn foo() {
    let y: float = 1.0
    let x: int = y
}
"#,
        ],
        [
            "lit_range",
            r#"
fn foo() {
    let i: int = 2147483648
}
"#,
        ],
    ];
    run_insta!("let", tests);
}

#[test]
fn test_unary() {
    let tests = [
        [
            "lit",
            r#"
fn foo() { -3 }
"#,
        ],
        [
            "var",
            r#"
fn foo() {
    let xy: int8 = 1
    -xy
}
"#,
        ],
        [
            "bad_type_1",
            r#"
fn foo() {
    -false
}
"#,
        ],
        [
            "bad_type_2",
            r#"
fn foo() {
    -'c'
}
"#,
        ],
    ];
    run_insta!("unary", tests);
}

#[test]
fn test_array() {
    let tests = [
        ["type", "let x: [int; 3]"],
        ["lit", "let x: [int; 3] = [1, 2, 3]"],
        [
            "lit_reassign",
            r#"
let x: [int; 3] = [1, 2, 3]
x = [4, 5, 6]
"#,
        ],
        ["lit_bad_1", "let x: [int; 3] = [1, 2.0, 3]"],
        ["lit_bad_2", "let x: [float; 3] = [1, 2, 3]"],
        ["lit_bad_3", "let x: [int; 2] = [1, 2, 3]"],
        ["empty_lit", "let x: [int; 3] = []"],
        [
            "index_1",
            r#"
let x: [int; 3] = [1, 2, 3]
x[0]
"#,
        ],
        [
            "index_2",
            r#"
let x: [int; 3] = [1, 2, 3]
x[1 + 2]
"#,
        ],
        [
            "index_3",
            r#"
let x: [int; 3] = [1, 2, 3]
let y: int = 1
x[y]
"#,
        ],
        [
            "index_4",
            r#"
let x: [int; 3] = [1, 2, 3]
x[1] = 7
"#,
        ],
        [
            "index_bad_1",
            r#"
let x: [int; 3] = [1, 2, 3]
let y: float = 1.0
x[y]
"#,
        ],
        [
            "index_bad_2",
            r#"
let x: [int; 3] = [1, 2, 3]
x['c']
"#,
        ],
        [
            "index_bad_3",
            r#"
let x: [int; 3] = [1, 2, 3]
let y: int8 = 1
x[y]
"#,
        ],
    ];

    run_insta!("array", tests)
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
"#,
        ],
        [
            "delete_scope",
            r#"
fn foo(a: int) -> int {
    let b: int = 1
    {
        let c: int = 2
    }
    c
}
"#,
        ],
        [
            "for_scope",
            r#"
let x: float = 1.0
for x: int = 1; x < 10; 1 {
    x
}
x
"#,
        ],
        [
            "if_scope",
            r#"
let x: float = 1.0
if x < 2.0 {
    let y: int = 2
    x
}
y
"#,
        ],
        [
            "if_else_scope",
            r#"
let x: float = 1.0
if x < 2.0 {
    let y: int = 2
    x
} else {
    -y
}
"#,
        ],
    ];
    run_insta!("scope", tests);
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
        a
    }
    fn d() {}
}
"#,
        ],
    ];
    run_insta!("struct", tests)
}

#[test]
fn test_tyc_int_no_hint() {
    use Literal::*;

    let literals = [
        (UInt64(7), Ok(Type::Int32)),
        (UInt64(i32::MAX as u64), Ok(Type::Int32)),
        (UInt64(i32::MAX as u64 + 1), Err(ERR_STR)),
        (Float(7.0), Ok(Type::Float)),
    ];

    let mut symbol_table = SymbolTable::new();
    let mut tc = TypeChecker::new(&mut symbol_table);
    for lit in literals {
        let res = tc.check_lit(ast::Lit { value: lit.0 }, None).map(|e| e.ty().cloned().unwrap_or_default());
        assert_eq!(res, lit.1.map_err(|x| x.to_string()));
    }
}

#[test]
fn test_tyc_int_with_hint() {
    use Literal::*;

    let literals = [
        (UInt64(7), Type::Int8, Ok(Type::Int8)),
        (UInt64(i8::MAX as u64), Type::Int8, Ok(Type::Int8)),
        (UInt64(i8::MAX as u64 + 1), Type::Int8, Err(ERR_STR)),
        (UInt64(7), Type::Int16, Ok(Type::Int16)),
        (UInt64(i16::MAX as u64), Type::Int16, Ok(Type::Int16)),
        (UInt64(i16::MAX as u64 + 1), Type::Int16, Err(ERR_STR)),
        (UInt64(7), Type::Int32, Ok(Type::Int32)),
        (UInt64(i32::MAX as u64), Type::Int32, Ok(Type::Int32)),
        (UInt64(i32::MAX as u64 + 1), Type::Int32, Err(ERR_STR)),
        (UInt64(7), Type::Int64, Ok(Type::Int64)),
        (UInt64(i64::MAX as u64), Type::Int64, Ok(Type::Int64)),
        (UInt64(i64::MAX as u64 + 1), Type::Int64, Err(ERR_STR)),
        (UInt64(7), Type::UInt8, Ok(Type::UInt8)),
        (UInt64(u8::MAX as u64), Type::UInt8, Ok(Type::UInt8)),
        (UInt64(u8::MAX as u64 + 1), Type::UInt8, Err(ERR_STR)),
        (UInt64(7), Type::UInt16, Ok(Type::UInt16)),
        (UInt64(u16::MAX as u64), Type::UInt16, Ok(Type::UInt16)),
        (UInt64(u16::MAX as u64 + 1), Type::UInt16, Err(ERR_STR)),
        (UInt64(7), Type::UInt32, Ok(Type::UInt32)),
        (UInt64(u32::MAX as u64), Type::UInt32, Ok(Type::UInt32)),
        (UInt64(u32::MAX as u64 + 1), Type::UInt32, Err(ERR_STR)),
        (UInt64(7), Type::UInt64, Ok(Type::UInt64)),
        (UInt64(u64::MAX as u64), Type::UInt64, Ok(Type::UInt64)),
        (Float(7.0), Type::Float, Ok(Type::Float)),
        (Float(7.0), Type::Double, Ok(Type::Double)),
    ];

    let mut symbol_table = SymbolTable::new();
    let mut tc = TypeChecker::new(&mut symbol_table);
    for lit in literals {
        let res = tc
            .check_lit(ast::Lit { value: lit.0 }, Some(&lit.1))
            .map(|e| e.ty().cloned().unwrap_or_default());
        assert_eq!(res, lit.2.map_err(|x| x.to_string()));
    }
}

// let x: $variant
// x + 3
macro_rules! test_lit_hint_binop_int {
    ($variant:ident) => {{
        let mut st = SymbolTable::new();
        st.insert(Symbol::new_var("x", &$variant));
        let mut tc = TypeChecker::new(&mut st);
        let lhs = ParsedNode::new_ident(String::from("x"));
        let rhs = ParsedNode::new_lit(Literal::UInt64(3));
        let res = tc
            .check_binop(ast::BinOp { op: Operator::Add, lhs: Box::new(lhs), rhs: Box::new(rhs) })
            .map(|e| e.ty().unwrap_or_default().clone());
        assert_eq!(res, Ok($variant));

        let mut st = SymbolTable::new();
        st.insert(Symbol::new_var("x", &$variant));
        let mut tc = TypeChecker::new(&mut st);
        let lhs = ParsedNode::new_lit(Literal::UInt64(3));
        let rhs = ParsedNode::new_ident(String::from("x"));
        let res = tc
            .check_binop(ast::BinOp { op: Operator::Add, lhs: Box::new(lhs), rhs: Box::new(rhs) })
            .map(|e| e.ty().unwrap_or_default().clone());
        assert_eq!(res, Ok($variant));
    }};
}

// let x: $variant
// x + 3.0
macro_rules! test_lit_hint_binop_float {
    ($variant:ident) => {{
        let mut st = SymbolTable::new();
        st.insert(Symbol::new_var("x", &$variant));
        let mut tc = TypeChecker::new(&mut st);
        let lhs = ParsedNode::new_ident(String::from("x"));
        let rhs = ParsedNode::new_lit(Literal::Float(3.0));
        let res = tc
            .check_binop(ast::BinOp { op: Operator::Add, lhs: Box::new(lhs), rhs: Box::new(rhs) })
            .map(|e| e.ty().unwrap_or_default().clone());
        assert_eq!(res, Ok($variant));

        let mut st = SymbolTable::new();
        st.insert(Symbol::new_var("x", &$variant));
        let mut tc = TypeChecker::new(&mut st);
        let lhs = ParsedNode::new_lit(Literal::Float(3.0));
        let rhs = ParsedNode::new_ident(String::from("x"));
        let res = tc
            .check_binop(ast::BinOp { op: Operator::Add, lhs: Box::new(lhs), rhs: Box::new(rhs) })
            .map(|e| e.ty().unwrap_or_default().clone());
        assert_eq!(res, Ok($variant));
    }};
}

#[test]
fn test_tyc_binop_lit() {
    use Type::*;

    test_lit_hint_binop_int!(Int8);
    test_lit_hint_binop_int!(Int16);
    test_lit_hint_binop_int!(Int32);
    test_lit_hint_binop_int!(Int64);
    test_lit_hint_binop_int!(UInt8);
    test_lit_hint_binop_int!(UInt16);
    test_lit_hint_binop_int!(UInt32);
    test_lit_hint_binop_int!(UInt64);
    test_lit_hint_binop_float!(Float);
    test_lit_hint_binop_float!(Double);
}
