use insta::assert_yaml_snapshot;
use insta::glob;
use std::fs;

use lightc::lexer::*;

#[test]
fn test_lexer() {
    glob!("inputs/*.input", |path| {
        let input = fs::read_to_string(path).unwrap();
        assert_yaml_snapshot!(Lexer::new(&input).collect::<Result<Vec<_>, _>>());
    });
}

#[test]
fn test_lexer_err_num() {
    let input = "let foo = 1b4";
    assert_eq!(
        Lexer::new(input).collect::<Result<Vec<_>, _>>(),
        Err(LexError::InvalidNum)
    );
}
