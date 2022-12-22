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

struct BuildEnv {
    args: CliArgs,
    root_dir: PathBuf,
    build_dir: PathBuf,
}

impl BuildEnv {
    fn new() -> Self {
        let (root_dir, build_dir) = Self::setup_build_env().expect("Error setting up build environment");
        BuildEnv { args: CliArgs::parse(), root_dir, build_dir }
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
}

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

fn main() {
    let env = BuildEnv::new();
    let files = env.args.files.clone();

    let mut parsed_module_map: HashMap<String, ParsedModule> = HashMap::new();
    for file in files {
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

    if env.args.show_tokens {
        println!("Tokens:");
        parsed_module_map.iter().for_each(|(name, module)| {
            println!("  module: {:?}", name);
            module.tokens.iter().for_each(|t| println!("    {}", t));
        });
        println!();
    }

    if env.args.show_ast {
        println!("AST:");
        parsed_module_map.iter().for_each(|(name, module)| {
            println!("  module: {:?}", name);
            module.ast.nodes().iter().for_each(|n| println!("    {}", n));
        });
        println!();
    }

    // if module_map.len() > 1 && env.args.compile_only && env.args.output.is_some() {
    //     eprintln!("Can't use `-c` and `-o` with multiple modules");
    // }

    let mut object_module_map = HashMap::new();
    for (module_name, mut module) in parsed_module_map {
        // Type checker
        let typed_ast = Tych::new(&mut module.symbol_table).walk(module.ast).unwrap_or_else(|e| {
            eprintln!("Type checking error: {}", e);
            process::exit(1);
        });

        if env.args.show_typed_ast {
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

        if env.args.show_hir {
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
            Codegen::run(hir, &module_name, module.symbol_table, env.build_dir.clone(), &env.args, false)
                .unwrap_or_else(|e| panic!("Error compiling module `{}`: {}", module_name, e))
                .as_file_path();

        object_module_map.insert(module_name, object_file);
    }

    // If we just want the object file, copy it/them up to the root and exit
    if env.args.compile_only {
        if let Some(filename) = env.args.output {
            let object_file = &object_module_map.into_values().collect::<Vec<_>>()[0];
            fs::copy(object_file.clone(), filename)
                .expect(&format!("Error copying object file: {}", object_file.to_string_lossy()));
        } else {
            for (_, object_file) in &object_module_map {
                fs::copy(object_file, object_file.file_name().unwrap())
                    .expect(&format!("Error copying object file: {}", object_file.to_string_lossy()));
            }
        }
        process::exit(0);
    }

    Command::new("clang")
        .arg("-o")
        .arg("a.out")
        .args(object_module_map.into_values())
        //.arg("stdlib/stdlib.o")
        .arg("-lm")
        .spawn()
        .expect("Error compiling")
        .wait()
        .expect("Error waiting on clang");
}

// fn get_module_name(path: &Path) -> String {
//     path.with_extension("")
//         .file_name()
//         .expect("Error getting source filename")
//         .to_str()
//         .expect("Error getting module name")
//         .to_owned()
// }

// // Derive the output file name
// fn derive_output_name(env: BuildEnv, object_map: HashMap<String, PathBuf>) -> String {
//     // let outfile = match (env.args.output, env.args.compile_only) {
//     //     (Some(name), _) => PathBuf::from(name),
//     //     (None, true) => {
//     //         let mut obj_file = env.root_dir;
//     //         obj_file.push(&module_name);
//     //         obj_file.as_path().with_extension("o")
//     //     }
//     //     (None, false) => PathBuf::from("a.out"),
//     // };
//     unimplemented!()
// }
