use clap::Parser as Clap;
use inkwell::{
    context::Context,
    module::Module,
    passes::PassManager,
    targets::{FileType, InitializationConfig, Target, TargetMachine},
    OptimizationLevel,
};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::{env, fs, process};

use codegen::Codegen;
use common::SymbolTable;
use hir::Hir;
use lexer::Lexer;
use parser::Parser;
use type_checker::TypeChecker;

mod jit_externs;

fn main() {
    let args = Args::parse();
    let source = fs::read_to_string(args.file.as_path()).expect("Error opening file");
    let module_name = get_module_name(&args.file);
    let (root_dir, build_dir) = setup_build_env().expect("Error setting up build environment");
    let mut symbol_table = SymbolTable::new();

    // Lexer
    let tokens = Lexer::new(&source).scan().unwrap_or_else(|e| {
        eprintln!("Lexing error: {}", e);
        process::exit(1);
    });

    if args.tokens {
        println!("Tokens:");
        tokens.iter().for_each(|t| println!("{:?}", t));
        println!();
    }

    // Parser
    let parser = Parser::new(&tokens, &mut symbol_table);
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

    // Type checker
    let tyst = TypeChecker::new(&mut symbol_table).walk(ast).unwrap_or_else(|e| {
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

    // HIR
    let hir = Hir::new(&mut symbol_table).walk(tyst).unwrap_or_else(|e| {
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

    // Codegen
    let context = Context::create();
    let builder = context.create_builder();
    let module = context.create_module(&module_name);
    let target_machine = set_target_machine(&module);
    let fpm = PassManager::create(&module);
    let codegen = Codegen::new(
        &context,
        &builder,
        &module,
        &fpm,
        &symbol_table,
        args.opt_level,
        args.no_verify,
        !args.compile,
    );
    codegen.walk(hir).expect("Compiler error");

    if args.show_ir {
        println!("IR:");
        println!("{}", module.print_to_string().to_string());
    }

    if args.jit {
        run_jit(&module);
        process::exit(0);
    }

    // File name for module binary
    let mut module_file = build_dir;
    module_file.push(&module_name);
    let module_file = module_file.as_path().with_extension("o");

    // Write the object file to the build directory
    target_machine.write_to_file(&module, FileType::Object, &module_file).expect("Error writing object file");

    // If we just want the object file, copy it up to the root and exit
    if args.compile {
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

// Optimizes for host CPU
// TODO: Make more generic
fn set_target_machine(module: &Module) -> TargetMachine {
    Target::initialize_x86(&InitializationConfig::default());
    let triple = TargetMachine::get_default_triple();
    let target = Target::from_triple(&triple).expect("Target error");
    let target_machine = target
        .create_target_machine(
            &triple,
            &TargetMachine::get_host_cpu_name().to_string(),
            &TargetMachine::get_host_cpu_features().to_string(),
            OptimizationLevel::Default,
            inkwell::targets::RelocMode::Default,
            inkwell::targets::CodeModel::Default,
        )
        .expect("Target machine error");

    module.set_data_layout(&target_machine.get_target_data().get_data_layout());
    module.set_triple(&triple);
    target_machine
}

fn run_jit(module: &Module) {
    jit_externs::load();

    let ee = module.create_jit_execution_engine(OptimizationLevel::None).unwrap();

    let f = unsafe { ee.get_function::<unsafe extern "C" fn() -> i64>("main") };
    match f {
        Ok(f) => unsafe {
            let ret = f.call();
            eprintln!("main() return value: {:?}", ret);
        },
        Err(e) => {
            eprintln!("Execution error: {}", e);
        },
    };
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

#[derive(Clap, Debug)]
struct Args {
    /// Display tokens
    #[clap(long, parse(from_flag))]
    tokens: bool,

    /// Display AST
    #[clap(long, parse(from_flag))]
    show_ast: bool,

    /// Display TYped aST
    #[clap(long, parse(from_flag))]
    show_tyst: bool,

    /// Display HIR
    #[clap(long, parse(from_flag))]
    show_hir: bool,

    /// Display IR
    #[clap(long, parse(from_flag))]
    show_ir: bool,

    /// Run jit rather than outputting a binary
    #[clap(short, long, parse(from_flag))]
    jit: bool,

    /// Output to <file>
    #[clap(short, long, value_name = "file")]
    output: Option<String>,

    /// Optimization level
    #[clap(short = 'O', long, value_name="level", default_value_t = 1, parse(try_from_str=valid_opt_level))]
    opt_level: usize,

    /// Disable LLVM function validation (useful for debugging)
    #[clap(short, long, parse(from_flag))]
    no_verify: bool,

    /// Input file
    #[clap(parse(from_os_str))]
    file: PathBuf,

    /// Compile and output object file
    #[clap(short, long, parse(from_flag))]
    compile: bool,
}

fn valid_opt_level(s: &str) -> Result<usize, String> {
    let opt_level = s.parse().map_err(|_| format!("`{}` isn't an optimization level", s))?;

    if (0..=1).contains(&opt_level) {
        Ok(opt_level)
    } else {
        Err("Must be one of: 0 (none), 1 (basic)".to_string())
    }
}
