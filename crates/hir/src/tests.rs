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
