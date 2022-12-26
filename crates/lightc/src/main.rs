use clap::Parser as Clap;
use std::collections::HashMap;
use std::path::PathBuf;
use std::process::Command;
use std::{env, fs, process};

use codegen::Codegen;
use common::CliArgs;
use lex::Lex;
use lower::Lower;
use module::Module;
use parse::Parse;
use tych::Tych;

mod module;

const STDLIB_PATH: &str = "core/";

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
        .arg("core/core.o")
        .arg("-lm")
        .spawn()
        .expect("Error compiling")
        .wait()
        .expect("Error waiting on clang");
}

fn main() {
    let (root_dir, build_dir) = setup_build_env().expect("Error setting up build environment");
    let args = CliArgs::parse();

    // Lex and parse one file at a time. Merge the resulting tokens and symbols into a
    // Module
    let mut module_map: HashMap<String, Module> = HashMap::new();
    for file in &args.files {
        let source = fs::read_to_string(file.as_path())
            .unwrap_or_else(|_| panic!("Error opening file: {}", file.to_string_lossy()));

        // Lexer
        let tokens = Lex::new(&source).scan().unwrap_or_else(|e| {
            eprintln!("Lexing error: {}", e);
            process::exit(1);
        });

        // Parser
        let mut parser = Parse::new(&tokens);
        let ast = parser.parse().unwrap_or_else(|e| {
            eprintln!("Parsing error: {}", e);
            process::exit(1);
        });

        // Get the existing module or create and insert an empty one
        let module_name = parser.module_name();
        let module = module_map.entry(module_name.to_owned()).or_insert(Module::new(module_name));

        // xxx test
        // Merge symbols into module map
        parser.merge_symbols(&mut module.symbol_table).unwrap_or_else(|e| {
            eprintln!("Error merging parsed symbols: {}", e);
            process::exit(1);
        });

        // Merge tokens, AST and, imports for each module
        // TODO: Dedup imports
        module.tokens.append(&mut tokens.clone());
        module.ast.append(ast);
        module.imports.append(&mut parser.imports().to_vec())
    }

    // Side effect of displaying the aggregates outside the loop is that parsing needs to
    // be successful to show tokens
    if args.show_tokens {
        println!("Tokens:");
        module_map.iter().for_each(|(name, module)| {
            println!("  module: {:?}", name);
            module.tokens.iter().for_each(|t| println!("    {}", t));
        });
        println!();
    }

    if args.show_ast {
        println!("AST:");
        module_map.iter().for_each(|(name, module)| {
            println!("  module: {:?}", name);
            module.ast.nodes().iter().for_each(|n| println!("    {}", n));
        });
        println!();
    }

    // Produce an object file for each module. Add to Module
    for (module_name, mut module) in &mut module_map {
        // Resolve imported symbols
        let import_symbols = module.resolve_imports(STDLIB_PATH).expect("Error resolving imports");

        // Type checker
        let typed_ast = Tych::new(&mut module.symbol_table).walk(module.ast.clone()).unwrap_or_else(|e| {
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
        let hir = Lower::new(import_symbols, &mut module.symbol_table).walk(typed_ast).unwrap_or_else(|e| {
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
            Codegen::run(hir, &module_name, module.symbol_table.clone(), build_dir.clone(), &args, false)
                .unwrap_or_else(|e| panic!("Error compiling module `{}`: {}", module_name, e))
                .as_file_path();

        module.object_file = object_file;
    }

    // Handle various permutations of command line arguments
    // TODO: Create interfaces and archives whenever `-c` is specified
    match (module_map.len() > 1, args.compile_only, args.output) {
        // Output a.out
        (_, false, None) => link(
            "a.out",
            &[module_map
                .get("main")
                .expect("Linking error: no `main` module for executable")
                .object_file
                .clone()],
        ),
        // Output `args.output` exec
        (_, false, Some(filename)) => {
            link(&filename, &module_map.into_values().map(|m| m.object_file).collect::<Vec<_>>())
        },
        // Copy to `module_name`.o
        (false, true, None) => {
            let mut output_file = root_dir;
            let (module_name, module) = &module_map.drain().collect::<Vec<(String, Module)>>()[0];
            output_file.push(&module_name);
            fs::copy(module.object_file.clone(), output_file.with_extension("o"))
                .expect(&format!("Error copying object file: {}", module.object_file.to_string_lossy()));

            // Write interface file
            module.create_interface().expect("Error creating interface file");
        },
        // Copy to `args.output`.o
        (false, true, Some(filename)) => {
            let mut output_file = root_dir;
            let (_, object_file) = &module_map
                .drain()
                .map(|(name, module)| (name, module.object_file))
                .collect::<Vec<(String, PathBuf)>>()[0];
            output_file.push(filename);
            fs::copy(object_file, output_file.with_extension("o"))
                .expect(&format!("Error copying object file: {}", object_file.to_string_lossy()));
        },
        // Copy to multiple object files
        (true, true, None) => {
            for (_, module) in &module_map {
                fs::copy(module.object_file.clone(), module.object_file.file_name().unwrap())
                    .expect(&format!("Error copying object file: {}", module.object_file.to_string_lossy()));
            }
        },
        // Output `args.output`.o
        (true, true, Some(filename)) => {
            link(&filename, &module_map.into_values().map(|m| m.object_file).collect::<Vec<_>>())
        },
    };
}
