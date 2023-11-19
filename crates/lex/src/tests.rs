use super::*;

macro_rules! run_insta {
    ($prefix:expr, $tests:expr) => {
        insta::with_settings!({ snapshot_path => "tests/snapshots", prepend_module_to_snapshot => false }, {
            for test in $tests {
                let tokens = Lex::new(test[1]).scan();
                insta::assert_yaml_snapshot!(format!("{}_{}", $prefix, test[0]), (test[1], tokens));
            }
        })
    };
}

#[test]
fn test_char() {
    let tests = [
        ["basic", "'c'"],
        ["ctl", "'\\n'"],
        ["unterminated", "'c"],
        ["too_many", "'mm'"],
        ["single_quote", "'"],
        ["bad_ctl", "'\\c'"],
        ["empty", "''"],
        ["unknown", "let foo = `1`"],
    ];
    run_insta!("char", tests);
}

#[test]
fn test_cond() {
    let tests = [
        [
            "if_only",
            r#"
if x > -3 {
    print(x)
}
"#,
        ],
        [
            "if_else",
            r#"
if x > -3 {
    print(x)
} else {
    exit()
}
"#,
        ],
        [
            "if_else_if_else",
            r#"
if x > 3 {
    print(x)
} else if y == 1 {
    exit()
} else {
    z
}
"#,
        ],
    ];
    run_insta!("cond", tests);
}

#[test]
fn test_extern() {
    let tests = [["basic", "extern cos(x)"]];
    run_insta!("extern", tests);
}

#[test]
fn test_fn() {
    let tests = [[
        "basic",
        r#"
fn foo(a, b, c) -> int {
    bar(a) + 2
}
"#,
    ]];
    run_insta!("fn", tests);
}

#[test]
fn test_for() {
    let tests = [[
        "basic",
        r#"
for let x = 1; x < 10; 1 {
    print(x)
}
"#,
    ]];
    run_insta!("for", tests);
}

#[test]
fn test_logical_ops() {
    let tests = [["and", "x && y"], ["or", "x || y"], ["eq", "x == y"]];
    run_insta!("logical_ops", tests);
}

#[test]
fn test_loop() {
    let tests = [[
        "basic",
        r#"
loop {
    print(x)
}
"#,
    ]];
    run_insta!("loop", tests);
}

#[test]
fn test_let() {
    let tests = [
        ["int", "let a: int = 1"],
        ["int32", "let b: int32 = 2"],
        ["int64", "let b: int64 = 3"],
        ["uint", "let b: uint = 4"],
        ["uint32", "let b: uint32 = 5"],
        ["uint64", "let b: uint64 = 6"],
        ["float", "let c: float = 7.0"],
        ["double", "let c: double = 8.0"],
        ["bool_true", "let d: bool = true"],
        ["bool_false", "let d: bool = false"],
        ["char", "let e: char = 'c'"],
        ["char_ctl", "let e: char = '\n'"],
    ];
    run_insta!("let", tests);
}

#[test]
fn test_comment() {
    let tests = [
        [
            "basic",
            r#"
// line1
let foo = 14
foo
"#,
        ],
        [
            "multi_line",
            r#"
let foo = 14
// line1
// line2
foo
"#,
        ],
        [
            "trailing",
            r#"
let foo = 13
// line2"#,
        ],
        [
            "eol",
            r#"
let foo = 13 // line1"#,
        ],
        [
            "eol1",
            r#"
if foo { // line1"#,
        ],

    ];

    run_insta!("comment", tests);
}

#[test]
fn test_ops() {
    let tests = [["basic", "(x + y) * 4 / 4"], ["more", "x ^ 3 | 7 & 3"], ["and_more", "x++; y -= 1"]];
    run_insta!("ops", tests);
}

#[test]
fn test_semi() {
    let tests = [
        ["ident", "a"],
        ["num", "1"],
        ["call", "a()"],
        ["block", "{ a }"],
        ["let", "let a: int"],
        ["keyword_1", "let"],
        ["keyword_2", "fn"],
        ["char_lit", "'c'"],
    ];
    run_insta!("semi", tests);
}

#[test]
fn test_sarray() {
    let tests = [["type", "[int; 3]"], ["lit", "[1, 2, 3]"], ["index", "foo[0]"]];
    run_insta!("array", tests);
}

#[test]
fn test_while() {
    let tests = [[
        "basic",
        r#"
while i < 1 {
    i += 1
}
"#,
    ]];
    run_insta!("while", tests);
}

#[test]
fn test_lex_one() {
    use Operator::*;
    use TokenType::*;

    let input = r#"
foo + bar
// bar
/ not_a_comment
baz
foo::bar
"#;
    let mut lexer = Lex::new(input);

    assert_eq!(lexer.lex(), Ok(Token::new(Ident("foo".to_string()), 2, 1)));
    assert_eq!(lexer.lex(), Ok(Token::new(Op(Add), 2, 5)));
    assert_eq!(lexer.lex(), Ok(Token::new(Ident("bar".to_string()), 2, 7)));
    assert_eq!(lexer.lex(), Ok(Token::new(Op(Div), 4, 1)));
    assert_eq!(lexer.lex(), Ok(Token::new(Ident("not_a_comment".to_string()), 4, 3)));
    assert_eq!(lexer.lex(), Ok(Token::new(Ident("baz".to_string()), 5, 1)));
    assert_eq!(lexer.lex(), Ok(Token::new(Ident("foo::bar".to_string()), 6, 1)));
    assert_eq!(lexer.lex(), Ok(Token::new(Eof, 7, 1)));
}

#[test]
fn test_stream_next() {
    let input = r#"
abc
def
ghi
"#;
    let mut stream = StreamIter::new(input);
    assert_eq!(ContextElement::new('\n', 0, 0), stream.next().unwrap());
    assert_eq!(ContextElement::new('a', 1, 0), stream.next().unwrap());
    assert_eq!(ContextElement::new('b', 1, 1), stream.next().unwrap());
    assert_eq!(ContextElement::new('c', 1, 2), stream.next().unwrap());
    assert_eq!(ContextElement::new('\n', 1, 3), stream.next().unwrap());
    assert_eq!(ContextElement::new('d', 2, 0), stream.next().unwrap());
    assert_eq!(ContextElement::new('e', 2, 1), stream.next().unwrap());
    assert_eq!(ContextElement::new('f', 2, 2), stream.next().unwrap());
    assert_eq!(ContextElement::new('\n', 2, 3), stream.next().unwrap());
    assert_eq!(ContextElement::new('g', 3, 0), stream.next().unwrap());
    assert_eq!(ContextElement::new('h', 3, 1), stream.next().unwrap());
    assert_eq!(ContextElement::new('i', 3, 2), stream.next().unwrap());
    assert_eq!(ContextElement::new('\n', 3, 3), stream.next().unwrap());
    assert_eq!(ContextElement::new(0 as char, 4, 0), stream.next().unwrap());
    assert_eq!(ContextElement::new(0 as char, 4, 0), stream.next().unwrap());
}
