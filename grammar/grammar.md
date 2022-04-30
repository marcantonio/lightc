## Light Grammar
Formal grammar for light. It's written as a modified form of EBNF. Deviations from EBNF should be obvious are mainly for more concise ranges and repetition, similar to the [W3C's notation](https://www.w3.org/TR/xquery-31/#EBNFNotation).

Note that while semicolons are part of the formal grammar for simplicity, they are optional in practice. Similar to Swift and Go, they are inserted by the lexer when appropriate.

``` ebnf
Program     ::= StmtList ;
StmtList    ::= ( Stmt ';' )+ ;
Stmt        ::= LetStmt
              | ForStmt
              | FnDecl
              | ExternDecl
              | Expr ;
Block       ::= '{' StmtList? '}' ;
FnDecl      ::= Prototype Block ;
ExternDecl  ::= 'extern' Prototype ;
Prototype   ::= 'fn' ident '(' ( TypedDecl ( ',' TypedDecl )* )* ')' ( '->' type )? ;
ForStmt     ::= 'for' VarDecl ';' Expr ';' number? Block ;
LetStmt     ::= 'let' VarDecl ;
VarDecl     ::= TypedDecl '=' Expr ;
TypedDecl   ::= ident ':' type ;
Expr        ::= UnopExpr
              | Expr mul_op UnopExpr
              | Expr add_op UnopExpr
              | Expr rel_op UnopExpr
              | Expr '&&' UnopExpr
              | Expr '||' UnopExpr ;
PrimaryExpr ::= CondExpr
              | LitExpr
              | IdentExpr
              | Assignment
              | ParenExpr ;
Assignment  ::= IdentExpr '=' Expr ;
UnopExpr    ::= PrimaryExpr
              | ( '-' | '!' ) UnopExpr ;
LitExpr     ::= number | bool ;
IdentExpr   ::= ident ;
ParenExpr   ::= '(' Expr ')' ;
CondExpr    ::= 'if' Expr Block ( 'else' (CondExpr | Block ) )? ;

type        ::= 'int' | 'int8' | 'int16' | 'int32' | 'int64'
              | 'uint' | 'uint8' | 'uint16' | 'uint32' | 'uint64'
              | 'float' | 'double' | 'bool' | 'char' ;
bool        ::= 'true' | 'false' ;
ident       ::= letter ( letter | digit | '_' )*;
bin_op      ::= '||' | '&&' | rel_op | add_op | mul_op ;
rel_op      ::= '>' | '<' | '==' ;
add_op      ::= '+' | '-' ;
mul_op      ::= '*' | '/' ;
number      ::= integer | float ;
integer     ::= digit+ ;
float       ::= digit '.' digit ;
letter      ::= [a-zA-Z] ;
digit       ::= [0-9] ;
whitespace  ::= [ \t\r\n] ;
comment     ::= '//' [^\r\n]* [\r\n] ;
```

## Exceptions
`StmtList ::= ( Stmt ';' )+ ;` - A semicolon is optional when a closing '}' is present. This allows for concise one-liners.

## Testing and changes
The grammar is also present in `light.g4` for testing and validation. Testing can be done by running `./test-grammar.sh` in this directory.

Once completed, the grammar was translated to it's current form through a mostly manual process. I did run it through https://bottlecaps.de/convert, and then undid some of the factorization and formatting.
