## Light Grammar
Formal grammar for light. It's written as a modified form of EBNF. Deviations from EBNF should be obvious are mainly for more concise ranges and repetition, similar to the [W3C's notation](https://www.w3.org/TR/xquery-31/#EBNFNotation).

Note that while semicolons are part of the formal grammar for simplicity, they are optional in practice. Similar to Swift and Go, they are inserted by the lexer when appropriate.

```ebnf
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
Prototype   ::= 'fn' ident '(' ( TypedDecl ( ',' TypedDecl )* )* ')' ( '->' TypeAntn )? ;
ForStmt     ::= 'for' TypedDecl '=' Expr ';' Expr ';' number? Block ;
LetStmt     ::= 'let' TypedDecl ( '=' Expr  )? ;
TypedDecl   ::= ident ':' TypeAntn ;
TypeAntn    ::= type | '[' type ']' ;
Expr        ::= PrimaryExpr
              | Expr mul_op Expr
              | Expr add_op Expr
              | Expr rel_op Expr
              | Expr bit_op Expr
              | Expr '&&' Expr
              | Expr '||' Expr
              | IdentExpr '=' Expr ;
PrimaryExpr ::= CondExpr
              | LitExpr
              | IdentExpr
              | CallExpr
              | Block
              | ParenExpr
              | UnopExpr
              | IndexExpr ;
UnopExpr    ::= ( '-' | '!' ) Expr ;
LitExpr     ::= number | bool | CharLit | ArrayLit ;
CallExpr    ::= ident '(' ExprList? ')' ;
ParenExpr   ::= '(' Expr ')' ;
CondExpr    ::= 'if' Expr Block ( 'else' (CondExpr | Block ) )? ;
IdentExpr   ::= ident ;
IndexExpr   ::= PrimaryExpr '[' Expr ']' ;
ArrayLit    ::= '[' ExprList? ']' ;
CharLit     ::= char ;
ExprList    ::= Expr ','? | Expr ( ',' Expr )* ;

type        ::= 'int' | 'int8' | 'int16' | 'int32' | 'int64'
              | 'uint' | 'uint8' | 'uint16' | 'uint32' | 'uint64'
              | 'float' | 'double' | 'bool' | 'char' ;
bool        ::= 'true' | 'false' ;
ident       ::= letter ( letter | digit | '_' )* ;
bit_op      ::= '&' | '|' | '^' ;
eq_op       ::= '==' | '!=' ;
rel_op      ::= '>' | '>=' | '<' | '<=' ;
add_op      ::= '+' | '-' ;
mul_op      ::= '*' | '/' ;
number      ::= integer | float ;
integer     ::= digit+ ;
float       ::= digit '.' digit ;
digit       ::= [0-9] ;
char        ::= "'" ( [^'\\r\n\t] | '\' [rnt0] ) "'" ;
letter      ::= [a-zA-Z] ;
whitespace  ::= [ \t\r\n] ;
comment     ::= '//' [^\r\n]* [\r\n] ;
```

## Notes
- `StmtList ::= ( Stmt ';' )+ ;` - A semicolon is optional when a closing '}' is present. This allows for concise one-liners.

## Testing and changes
The grammar is also present in `light.g4` for testing and validation. Testing can be done by running `./test-grammar.sh` in this directory.

Once completed, the grammar was translated to it's current form through a mostly manual process. I did run it through https://bottlecaps.de/convert, and then undid some of the factorization and formatting.
