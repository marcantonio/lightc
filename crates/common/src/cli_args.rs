use clap::Parser as Clap;
use std::path::PathBuf;

#[derive(Clap, Debug)]
pub struct CliArgs {
    /// Display tokens
    #[clap(long, parse(from_flag))]
    pub show_tokens: bool,

    /// Display AST
    #[clap(long, parse(from_flag))]
    pub show_ast: bool,

    /// Display Typed AST
    #[clap(long, parse(from_flag))]
    pub show_typed_ast: bool,

    /// Display HIR
    #[clap(long, parse(from_flag))]
    pub show_hir: bool,

    /// Display IR
    #[clap(long, parse(from_flag))]
    pub show_ir: bool,

    /// Run jit rather than outputting a binary
    #[clap(long, parse(from_flag))]
    pub run_jit: bool,

    /// Output to <file>
    #[clap(short, long, value_name = "file")]
    pub output: Option<String>,

    /// Optimization level
    #[clap(short = 'O', long, value_name="level", default_value_t = 1, parse(try_from_str=valid_opt_level))]
    pub opt_level: usize,

    /// Disable LLVM function validation (useful for debugging)
    #[clap(short, long, parse(from_flag))]
    pub no_verify: bool,

    /// Compile and output object file only, no linking
    #[clap(short, long, parse(from_flag))]
    pub compile_only: bool,

    /// Input file
    #[clap(parse(from_os_str))]
    pub file: PathBuf,
}

impl CliArgs {
    // For testing only
    pub fn new() -> Self {
        CliArgs {
            show_tokens: false,
            show_ast: false,
            show_typed_ast: false,
            show_hir: false,
            show_ir: false,
            run_jit: false,
            output: None,
            opt_level: 0,
            no_verify: false,
            compile_only: false,
            file: PathBuf::new(),
        }
    }
}

impl Default for CliArgs {
    fn default() -> Self {
        Self::new()
    }
}

fn valid_opt_level(s: &str) -> Result<usize, String> {
    let opt_level = s.parse().map_err(|_| format!("`{}` isn't an optimization level", s))?;

    if (0..=1).contains(&opt_level) {
        Ok(opt_level)
    } else {
        Err("Must be one of: 0 (none), 1 (basic)".to_string())
    }
}
