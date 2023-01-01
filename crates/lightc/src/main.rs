use clap::Parser as Clap;
use std::collections::HashMap;
use std::path::PathBuf;
use std::process::Command;
use std::{env, fs, process};

use codegen::Codegen;
use common::{CliArgs, SymbolTable};
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

// Extract all the object files from the module map and link everything
fn link(output: &str, module_map: HashMap<String, Module>) {
    let mut object_files = module_map.into_values().fold(vec![], |mut acc, mut m| {
        acc.push(m.object_file);
        acc.append(&mut m.import_objects);
        acc
    });
    object_files.sort();
    object_files.dedup();

    Command::new("clang")
        .arg("-o")
        .arg(output)
        .args(object_files)
        .arg("-lm")
        .spawn()
        .expect("Error compiling")
        .wait()
        .expect("Error waiting on clang");
}

fn main() {
    let (root_dir, build_dir) = setup_build_env().expect("Error setting up build environment");
    let args = CliArgs::parse();
    let mod_path = &[STDLIB_PATH, "scratch/"];
    let mut symbol_table = SymbolTable::new();

    // Lex and parse one file at a time. Merge the resulting tokens and symbols into a
    // Module
    let mut module_map: HashMap<String, Module> = HashMap::new();
    for file in &args.files {
        let source = fs::read_to_string(file.as_path())
            .unwrap_or_else(|err| panic!("Error opening `{}`: {}", file.to_string_lossy(), err));

        // Lexer
        let tokens = Lex::new(&source).scan().unwrap_or_else(|e| {
            eprintln!("Lexing error: {}", e);
            process::exit(1);
        });

        // Parser
        let (ast, module_name, mut imports) =
            Parse::new(&tokens, &mut symbol_table).parse().unwrap_or_else(|e| {
                eprintln!("Parsing error: {}", e);
                process::exit(1);
            });

        // Get the existing module or create and insert an empty one
        let module = module_map.entry(module_name.to_owned()).or_insert(Module::new(&module_name));

        // Merge tokens, AST, imports, and symbol table for each module
        // TODO: Dedup imports
        module.tokens.append(&mut tokens.clone());
        module.ast.append(ast);
        module.imports.append(&mut imports);
    }

    // Side effect of displaying the aggregates outside the loop is that parsing needs to
    // be successful to show tokens
    if args.show_tokens {
        println!("Tokens:");
        module_map.iter().for_each(|(name, module)| {
            println!(" module: {:?}", name);
            module.tokens.iter().for_each(|t| println!("  {}", t));
        });
        println!();
    }

    if args.show_ast {
        println!("AST:");
        module_map.iter().for_each(|(name, module)| {
            println!(" module: {:?}", name);
            module.ast.nodes().iter().for_each(|n| println!("  {}", n));
        });
        println!();
    }

    let available_modules = module_map.keys().cloned().collect::<Vec<_>>();

    // Produce an object file for each module. Add to Module
    for (module_name, mut module) in &mut module_map {
        // Resolve imported symbols
        module
            .resolve_imports(&available_modules, mod_path, &mut symbol_table)
            .expect("Error resolving imports");

        // Type checker
        let typed_ast =
            Tych::new(&module_name, &mut symbol_table).walk(module.ast.clone()).unwrap_or_else(|e| {
                eprintln!("Type checking error: {}", e);
                process::exit(1);
            });

        if args.show_typed_ast {
            println!("Typed AST:");
            println!(" module: {:?}", module_name);
            for node in typed_ast.nodes() {
                println!("  {}", node);
            }
            println!();
        }

        // Lower
        let hir = Lower::new(&module_name, &mut symbol_table).walk(typed_ast).unwrap_or_else(|e| {
            eprintln!("Lowering error: {}", e);
            process::exit(1);
        });

        if args.show_hir {
            println!("HIR:");
            println!(" module: {:?}", module_name);
            println!("  structs:");
            for node in hir.structs() {
                println!("   {}", node);
            }
            println!();
            println!("  functions:");
            for node in hir.functions() {
                println!("   {}", node);
            }
            println!();
            println!("  prototypes:");
            for node in hir.prototypes() {
                println!("   {}", node);
            }
            println!();
        }

        // Codegen
        let object_file =
            Codegen::run(hir, &module_name, symbol_table.clone(), build_dir.clone(), &args, false)
                .unwrap_or_else(|e| panic!("Error compiling module `{}`: {}", module_name, e))
                .as_file_path();

        module.object_file = object_file;
    }

    // Handle various permutations of command line arguments
    // TODO: Create interfaces and archives whenever `-c` is specified
    match (module_map.len() > 1, args.compile_only, args.output) {
        // Output a.out
        (_, false, None) => {
            // println!(">>{:?}", module_map.keys());
            // println!("{:?}", &module_map.clone().into_values().map(|m| m.object_file).collect::<Vec<_>>());
            link(
                "a.out",
                module_map,
                // &[module_map
                //     .get("main")
                //     .expect("Linking error: no `main` module for executable")
                //     .object_file
                //     .clone()],
            );
        },
        // Output `args.output` exec
        (_, false, Some(filename)) => {
            link(&filename, module_map);
        },
        // Copy to `module_name`.o
        (false, true, None) => {
            let mut output_file = root_dir;
            let (module_name, module) = &module_map.drain().collect::<Vec<(String, Module)>>()[0];
            output_file.push(&module_name);
            fs::copy(module.object_file.clone(), output_file.with_extension("o"))
                .expect(&format!("Error copying object file: {}", module.object_file.to_string_lossy()));

            // Write interface file
            module.create_interface(&symbol_table).expect("Error creating interface file");
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
            link(&filename, module_map);
        },
    };
}
