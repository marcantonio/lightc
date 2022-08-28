use std::path::{Path, PathBuf};
use std::process::Command;
use std::{env, fs, process};

use clap::Parser as Clap;

use codegen::Codegen;
use common::{CliArgs, SymbolTable};
use hir::Hir;
use lexer::Lexer;
use parser::Parser;
use type_checker::TypeChecker;

fn main() {
    let args = CliArgs::parse();
    let source = fs::read_to_string(args.file.as_path()).expect("Error opening file");
    let module_name = get_module_name(&args.file);
    let (root_dir, build_dir) = setup_build_env().expect("Error setting up build environment");
    let mut symbol_table = SymbolTable::new();

    // Lexer
    let tokens = Lexer::new(&source).scan().unwrap_or_else(|e| {
        eprintln!("Lexing error: {}", e);
        process::exit(1);
    });

    if args.show_tokens {
        println!("Tokens:");
        tokens.iter().for_each(|t| println!("{:?}", t));
        println!();
    }

    // Parser
    let parser = Parser::new(&tokens);
    let ast = parser.parse().unwrap_or_else(|e| {
        eprintln!("Paring error: {}", e);
        process::exit(1);
    });

    if args.show_ast {
        println!("AST:");
        for node in ast.nodes() {
            println!("{}", node);
        }
        println!();
    }

    // HIR
    let hir = Hir::new(&mut symbol_table).walk(ast).unwrap_or_else(|e| {
        eprintln!("Lowering error: {}", e);
        process::exit(1);
    });

    if args.show_hir {
        println!("HIR:");
        for node in hir.nodes() {
            println!("{}", node);
        }
        println!();
    }

    // Type checker
    let tyst = TypeChecker::new(&mut symbol_table).walk(hir).unwrap_or_else(|e| {
        eprintln!("Type checking error: {}", e);
        process::exit(1);
    });

    if args.show_tyst {
        println!("Typed AST:");
        for node in tyst.nodes() {
            println!("{}", node);
        }
        println!();
    }

    // Codegen
    let module_file = Codegen::run_pass(tyst, &module_name, &symbol_table, build_dir, &args, false)
        .unwrap_or_else(|_| panic!("Error compiling `{}`", args.file.display()))
        .as_file_path();

    // If we just want the object file, copy it up to the root and exit
    if args.compile_only {
        let mut obj_file = root_dir;
        obj_file.push(&module_name);
        let obj_file = obj_file.as_path().with_extension("o");

        fs::copy(module_file, obj_file).expect("Error copying object file");
        process::exit(0);
    }

    let outfile = match args.output {
        Some(file) => file,
        None => String::from("a.out"),
    };

    Command::new("clang")
        .arg("-o")
        .arg(outfile)
        .arg(module_file)
        .arg("stdlib/stdlib.o")
        .arg("-lm")
        .spawn()
        .expect("Error compiling")
        .wait()
        .expect("Error waiting on clang");
}

fn get_module_name(path: &Path) -> String {
    path.with_extension("")
        .file_name()
        .expect("Error getting source filename")
        .to_str()
        .expect("Error getting module name")
        .to_owned()
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
