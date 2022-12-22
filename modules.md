# A simple module system for Light via lightc

## About modules

1. Add `module foo` to each each file
2. Modules can be split across multiple files
3. Modules will be separate compilation units

> TODO: Consider module block syntax, i.e., multiple modules in a single file.

## Compilation

1. Lex and parse all source files specified
   - Find module name during parsing
   - Concatenate ASTs by module
   - Store ASTs and symbol tables by module name in a map
   - Error if no module name found
   - Prepend symbols with module name
   - Extract imports

2. Process imports
   - Ensure external modules are in available
   - Read external module symbols
   - Insert required symbols into relevent symbol tables

> TODO: Details on importing external modules

3. Type check, lower and codegen each module separately
   - During lowering, insert `extern`s for required symbols
   - Executables must have a `main` module with a `main()` function
   - Each module will produce an object in the `.build` directory

4. Linking

| >1 module | -c specified | -o specified | action      |
|-----------|--------------|--------------|-------------|
| \-        | no           | no           | `a.out`     |
| \-        | no           | yes          | `-o` exec   |
| no        | yes          | no           | mod_name.o  |
| no        | yes          | yes          | `-o` .o     |
| yes       | yes          | no           | multiple .o |
| yes       | yes          | yes          | error       |

## Module file format
