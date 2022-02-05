use insta::assert_yaml_snapshot;
use insta::glob;
use std::fs::File;
use std::io::BufRead;
use std::io::BufReader;

use lightc::lexer::Lexer;
use lightc::parser::*;

fn ast_to_string(ast: Result<&[AstNode], &String>) -> String {
    match ast {
        Ok(ast) => ast.iter().map(|x| x.to_string()).collect(),
        Err(err) => err.to_string(),
    }
}

#[test]
fn test_parser() {
    glob!("inputs/parser/*.input", |path| {
        let file = File::open(path).expect("Error reading input file");
        let reader = BufReader::new(file);

        // Each line of the input files is meant to be a separate test
        // case. Treat each as its own AST. Including `ast_string` in the output
        // makes it more readable.
        let asts = reader
            .lines()
            .map(|line| {
                let line = line.expect("Error reading input line");
                let tokens = Lexer::new(&line).collect::<Result<Vec<_>, _>>().unwrap();
                let ast = Parser::new(&tokens).parse();
                let ast_string = ast_to_string(ast.as_deref());
                (ast, ast_string)
            })
            .collect::<Vec<_>>();
        assert_yaml_snapshot!(asts);
    });
}
