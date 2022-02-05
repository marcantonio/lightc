use insta::assert_yaml_snapshot;
use insta::glob;
use std::fs;

use lightc::lexer::*;

#[test]
fn test_lexer() {
    glob!("inputs/lexer/*.input", |path| {
        let input = fs::read_to_string(path).unwrap();
        assert_yaml_snapshot!(Lexer::new(&input).collect::<Result<Vec<_>, _>>());
    });
}
