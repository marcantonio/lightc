use std::fs::File;
use std::io::{Read, Write};
use std::path::PathBuf;

use common::symbol_table::Symbolic;
use common::{Symbol, SymbolTable};
use lex::Token;
use parse::ast::{self, Ast};

#[derive(Debug, Clone)]
pub struct Module {
    name: String,
    pub tokens: Vec<Token>,
    pub ast: Ast<ast::Node>,
    pub symbol_table: SymbolTable<Symbol>,
    pub object_file: PathBuf,
    pub imports: Vec<String>,
    pub import_objects: Vec<PathBuf>,
}

// Container type for module related stuff needed during compilation
impl Module {
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_owned(),
            tokens: vec![],
            ast: Ast::new(),
            symbol_table: SymbolTable::new(),
            object_file: PathBuf::new(),
            imports: vec![],
            import_objects: vec![],
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

        let int_file = self.object_file.with_extension("i");
        let mut file = File::create(int_file.clone())
            .map_err(|err| format!("error opening `{}`: {}", int_file.display(), err))?;
        file.write_all(&output).map_err(|err| format!("error writing `{}`: {}", int_file.display(), err))?;

        Ok(())
    }

    // Read the interface files in `library_path`. Each should be named `import`.i
    pub fn resolve_imports(&mut self, mod_pathes: &[&str]) -> Result<Vec<String>, String> {
        let mut import_symbols = vec![];

        'found: for import in &self.imports {
            for &mod_path in mod_pathes {
                let path = [mod_path, import].iter().collect::<PathBuf>().with_extension("i");

                // Get symbols the interface file and locate the object file
                if path.exists() {
                    // Interface file
                    let mut file = File::open(path.as_path())
                        .map_err(|err| format!("error opening `{}`: {}", path.display(), err))?;
                    let mut bytes = vec![];
                    file.read_to_end(&mut bytes)
                        .map_err(|err| format!("error reading `{}`: {}", path.display(), err))?;
                    let symbols = bincode::deserialize::<Vec<(String, Symbol)>>(&bytes)
                        .map_err(|err| format!("error deserializing symbols: {}", err))?;

                    for (name, symbol) in symbols {
                        self.symbol_table.insert_with_name(&name, symbol);
                        import_symbols.push(name);
                    }

                    // Object file
                    let path = path.with_extension("o");
                    if path.exists() {
                        self.import_objects.push(path);
                    } else {
                        return Err(format!("can't find object file `{}`", path.display()));
                    }
                    continue 'found;
                }
            }
            return Err(format!("could not resolve `{}`", import));
        }

        Ok(import_symbols)
    }
}
