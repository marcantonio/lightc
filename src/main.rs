use light::*;
use std::fs;

fn main() {
    let mut tokens: Vec<Token> = vec![];
    let code = fs::read_to_string("/home/mas/Code/light/mm.lt").expect("Error opening file");

    tokens.append(&mut lexer(&code).expect("Error lexing"));
    println!("tokens: {:?}", tokens);

    let parser = Parser::new(&tokens);
    let ast = parser.parse().expect("Error parsing");
    println!("ast:");
    for node in ast {
        println!("{}", node);
    }
}
