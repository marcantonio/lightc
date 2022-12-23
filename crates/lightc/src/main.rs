use clap::Parser as Clap;
use parse::ast::{self, Ast};
use std::collections::HashMap;
use std::path::PathBuf;
use std::process::Command;
use std::{env, fs, process};

use codegen::Codegen;
use common::{CliArgs, Symbol, SymbolTable};
use lex::{Lex, Token};
use lower::Lower;
use parse::Parse;
use tych::Tych;

struct ParsedModule {
    tokens: Vec<Token>,
    ast: Ast<ast::Node>,
    symbol_table: SymbolTable<Symbol>,
}

impl ParsedModule {
    fn new() -> Self {
        Self { tokens: vec![], ast: Ast::new(), symbol_table: SymbolTable::new() }
    }
}

fn setup_build_env() -> std::io::Result<(PathBuf, PathBuf)> {
    let root_dir = env::current_dir()?;
    let mut build_dir = root_dir.clone();
    build_dir.push(".build");

    if build_dir.exists() {
        fs::remove_dir_all(&build_dir)?;
    }
    fs::create_dir(&build_dir)?;

    Ok((root_dir, build_dir))
}

fn link(output: &str, objects: &[PathBuf]) {
    Command::new("clang")
        .arg("-o")
        .arg(output)
        .args(objects)
        //.arg("stdlib/stdlib.o")
        .arg("-lm")
        .spawn()
        .expect("Error compiling")
        .wait()
        .expect("Error waiting on clang");
}

fn main() {
    let (root_dir, build_dir) = setup_build_env().expect("Error setting up build environment");
    let args = CliArgs::parse();

    let mut parsed_module_map: HashMap<String, ParsedModule> = HashMap::new();
    for file in &args.files {
        let source = fs::read_to_string(file.as_path())
            .unwrap_or_else(|_| panic!("Error opening file: {}", file.to_string_lossy()));

        // Lexer
        let mut tokens = Lex::new(&source).scan().unwrap_or_else(|e| {
            eprintln!("Lexing error: {}", e);
            process::exit(1);
        });

        // Parser
        let mut parser = Parse::new(&tokens);
        let ast = parser.parse().unwrap_or_else(|e| {
            eprintln!("Parsing error: {}", e);
            process::exit(1);
        });

        let module = parsed_module_map.entry(parser.module_name().to_owned()).or_insert(ParsedModule::new());

        // xxx test
        // Merge symbols into module map
        parser.merge_symbols(&mut module.symbol_table).unwrap_or_else(|e| {
            eprintln!("Error merging parsed symbols: {}", e);
            process::exit(1);
        });

        module.tokens.append(&mut tokens);
        module.ast.append(ast);
    }

    if args.show_tokens {
        println!("Tokens:");
        parsed_module_map.iter().for_each(|(name, module)| {
            println!("  module: {:?}", name);
            module.tokens.iter().for_each(|t| println!("    {}", t));
        });
        println!();
    }

    if args.show_ast {
        println!("AST:");
        parsed_module_map.iter().for_each(|(name, module)| {
            println!("  module: {:?}", name);
            module.ast.nodes().iter().for_each(|n| println!("    {}", n));
        });
        println!();
    }

    let mut object_module_map = HashMap::new();
    for (module_name, mut module) in parsed_module_map {
        // Type checker
        let typed_ast = Tych::new(&mut module.symbol_table).walk(module.ast).unwrap_or_else(|e| {
            eprintln!("Type checking error: {}", e);
            process::exit(1);
        });

        if args.show_typed_ast {
            println!("Typed AST:");
            for node in typed_ast.nodes() {
                println!("{}", node);
            }
            println!();
        }

        // Lower
        let hir = Lower::new(&mut module.symbol_table).walk(typed_ast).unwrap_or_else(|e| {
            eprintln!("Lowering error: {}", e);
            process::exit(1);
        });

        if args.show_hir {
            println!("HIR:\nstructs");
            for node in hir.structs() {
                println!("{}", node);
            }
            println!();
            println!("functions");
            for node in hir.functions() {
                println!("{}", node);
            }
            println!();
        }

        // Codegen
        let object_file =
            Codegen::run(hir, &module_name, module.symbol_table, build_dir.clone(), &args, false)
                .unwrap_or_else(|e| panic!("Error compiling module `{}`: {}", module_name, e))
                .as_file_path();

        object_module_map.insert(module_name, object_file);
    }

    // Handle various permutations of command line arguments
    match (object_module_map.len() > 1, args.compile_only, args.output) {
        // Output a.out
        (_, false, None) => link("a.out", &object_module_map.into_values().collect::<Vec<_>>()),
        // Output `args.output` exec
        (_, false, Some(filename)) => link(&filename, &object_module_map.into_values().collect::<Vec<_>>()),
        // Copy to `module_name`.o
        (false, true, None) => {
            let mut output_file = root_dir;
            let (module_name, object_file) =
                &object_module_map.drain().collect::<Vec<(String, PathBuf)>>()[0];
            output_file.push(&module_name);
            fs::copy(object_file, output_file.with_extension("o"))
                .expect(&format!("Error copying object file: {}", object_file.to_string_lossy()));
        },
        // Copy to `args.output`.o
        (false, true, Some(filename)) => {
            let mut output_file = root_dir;
            let (_, object_file) = &object_module_map.drain().collect::<Vec<(String, PathBuf)>>()[0];
            output_file.push(filename);
            fs::copy(object_file, output_file.with_extension("o"))
                .expect(&format!("Error copying object file: {}", object_file.to_string_lossy()));
        },
        // Copy to multiple object files
        (true, true, None) => {
            for (_, object_file) in &object_module_map {
                fs::copy(object_file, object_file.file_name().unwrap())
                    .expect(&format!("Error copying object file: {}", object_file.to_string_lossy()));
            }
        },
        // Output `args.output`.o
        (true, true, Some(filename)) => link(&filename, &object_module_map.into_values().collect::<Vec<_>>()),
    };
}
