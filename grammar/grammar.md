## Light Grammar
Formal grammar for light. It's written as a modified form of EBNF. Deviations from EBNF should be obvious are mainly for more concise ranges and repetition, similar to the [W3C's notation](https://www.w3.org/TR/xquery-31/#EBNFNotation).

Note that while semicolons are part of the formal grammar for simplicity, they are optional in practice. Similar to Swift and Go, they are inserted by the lexer when appropriate.

```ebnf:light.ebnf
```

## Exceptions
`StmtList ::= ( Stmt ';' )+ ;` - A semicolon is optional when a closing '}' is present. This allows for concise one-liners.

## Testing and changes
The grammar is also present in `light.g4` for testing and validation. Testing can be done by running `./test-grammar.sh` in this directory.

Once completed, the grammar was translated to it's current form through a mostly manual process. I did run it through https://bottlecaps.de/convert, and then undid some of the factorization and formatting.
