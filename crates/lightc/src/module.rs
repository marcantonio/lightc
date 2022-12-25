use std::io::Write;
use std::path::PathBuf;
use std::{fs::File, io::Read};

use common::symbol_table::Symbolic;
use common::{Symbol, SymbolTable};
use lex::Token;
use parse::ast::{self, Ast};

pub struct Module {
    name: String,
    pub tokens: Vec<Token>,
    pub ast: Option<Ast<ast::Node>>,
    pub symbol_table: SymbolTable<Symbol>,
    pub object_file: PathBuf,
    pub imports: Vec<String>,
}

// Container type for module related stuff needed during compilation
impl Module {
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_owned(),
            tokens: vec![],
            ast: Some(Ast::new()), // XXX
            symbol_table: SymbolTable::new(),
            object_file: PathBuf::new(),
            imports: vec![],
        }
    }

    // Create am interface file for module. The file contains a Vec of tuples containing
    // the symbols fully qualified name and the symbol itself
    pub fn create_interface(&self) -> Result<(), String> {
        let symbols = self
            .symbol_table
            .export_symbols()
            .iter()
            .map(|&sym| {
                let symbol_name = match sym.short_name() {
                    Some(name) => name.to_owned(),
                    None => {
                        return Err(format!(
                            "Unsupported symbol type for `{}` in `create_interface()`",
                            sym.name()
                        ))
                    },
                };
                Ok((format!("{}::{}", self.name, symbol_name), sym))
            })
            .collect::<Result<Vec<_>, String>>()?;

        let output =
            bincode::serialize(&symbols).map_err(|err| format!("error serializing symbols: {}", err))?;

        let mut file = File::create(self.object_file.with_extension("i"))
            .map_err(|err| format!("error opening `{}`: {}", self.object_file.display(), err))?;
        file.write_all(&output)
            .map_err(|err| format!("error writing `{}`: {}", self.object_file.display(), err))?;

        Ok(())
    }

    // Read the interface files in `library_path`. Each should be named `import`.i
    pub fn resolve_imports(&mut self, library_path: &str) -> Result<Vec<String>, String> {
        let mut import_symbols = vec![];
        for import in &self.imports {
            let path: PathBuf = [library_path, import].iter().collect();

            // Get symbols from interface file
            let mut file = File::open(path.with_extension("i"))
                .map_err(|err| format!("error opening `{}.i`: {}", path.display(), err))?;
            let mut bytes = vec![];
            file.read_to_end(&mut bytes)
                .map_err(|err| format!("error reading `{}.i`: {}", path.display(), err))?;
            let symbols = bincode::deserialize::<Vec<(String, Symbol)>>(&bytes)
                .map_err(|err| format!("error deserializing symbols: {}", err))?;

            for (name, symbol) in symbols {
                self.symbol_table.insert_with_name(&name, symbol);
                import_symbols.push(name);
            }
        }

        Ok(import_symbols)
    }
}
