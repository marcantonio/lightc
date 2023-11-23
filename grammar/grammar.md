## Light Grammar
Formal grammar for Light. It's written as a modified form of EBNF. Deviations from EBNF
should be obvious are mainly for more concise ranges and repetition, similar to the [W3C's
notation](https://www.w3.org/TR/xquery-31/#EBNFNotation).

Note that while semicolons are part of the formal grammar for simplicity, they are
optional in practice. Similar to Swift and Go, they are inserted by the lexer when
appropriate.

```ebnf
Program            ::= ModDecl? StmtList ;
StmtList           ::= ( Stmt ';' )+ ;
Stmt               ::= LetStmt
                     | ForStmt
                     | LoopStmt
                     | WhileStmt
                     | FnDecl
                     | ExternDecl
                     | StructDecl
                     | UseStmt
                     | BreakStmt
                     | NextStmt
                     | Expr ;
ModDecl            ::= 'module' ident ';' ;
Block              ::= '{' StmtList? '}' ;
FnDecl             ::= Prototype Block ;
ExternDecl         ::= 'extern' Prototype ;
StructDecl         ::= 'struct' ident '{' ( LetStmt ';' | FnDecl ';' )* '}' ;
Prototype          ::= 'fn' ident '(' ( TypedDecl ( ',' TypedDecl )* )* ')' ( '->' TypeAntn )? ;
ForStmt            ::= 'for' VarInit ';' Expr ';' number? Block ;
LoopStmt           ::= 'loop' Block ;
WhileStmt          ::= 'while' Expr Block ;
LetStmt            ::= 'let' VarInit ;
VarInit            ::= TypedDecl ( '=' Expr  )? ;
TypedDecl          ::= ident ':' TypeAntn ;
TypeAntn           ::= type | '[' type ']' ;
UseStmt            ::= 'use' ident ;
BreakStmt          ::= 'break' ;
NextStmt           ::= 'next' ;
Expr               ::= PrimaryExpr
                     | Expr mul_op Expr
                     | Expr add_op Expr
                     | Expr rel_op Expr
                     | Expr eq_op Expr
                     | Expr bit_op Expr
                     | Expr '&&' Expr
                     | Expr '||' Expr
                     | AssignableExpr assign_op Expr ;
PrimaryExpr        ::= CondExpr
                     | LitExpr
                     | IdentExpr
                     | CallExpr
                     | Block
                     | ParenExpr
                     | UnopExpr
                     | IndexExpr
                     | SelfExpr
                     | FieldSelectorExpr
                     | MethodSelectorExpr ;
UnopExpr           ::= ( '-' | '!' ) Expr ;
LitExpr            ::= number | bool | CharLit | StringLit | ArrayLit ;
CallExpr           ::= ident '(' ExprList? ')' ;
ParenExpr          ::= '(' Expr ')' ;
CondExpr           ::= 'if' Expr Block ( 'else' (CondExpr | Block ) )? ;
IdentExpr          ::= ident ;
AssignableExpr     ::= ( IdentExpr | IndexExpr | SelfExpr | FieldSelectorExpr ) ;
SelfExpr           ::= 'self' '.' ( IdentExpr | CallExpr ) ;
FieldSelectorExpr  ::= PrimaryExpr '.' IdentExpr ;
MethodSelectorExpr ::= PrimaryExpr '.' CallExpr ;
IndexExpr          ::= PrimaryExpr '[' Expr ']' ;
ArrayLit           ::= '[' ExprList? ']' ;
CharLit            ::= char ;
StringLit          ::= string ;
ExprList           ::= Expr ','? | Expr ( ',' Expr )* ;

type               ::= 'int' | 'int8' | 'int16' | 'int32' | 'int64'
                     | 'uint' | 'uint8' | 'uint16' | 'uint32' | 'uint64'
                     | 'float' | 'double' | 'bool' | 'char' ;
bool               ::= 'true' | 'false' ;
ident              ::= letter ( letter | digit | '_' | '::' )* ;
assign_op          ::= '=' | '+=' | '-=' ;
bit_op             ::= '&' | '|' | '^' ;
eq_op              ::= '==' | '!=' ;
rel_op             ::= '>' | '>=' | '<' | '<=' ;
add_op             ::= '+' | '-' ;
mul_op             ::= '*' | '/' ;
number             ::= integer | float ;
integer            ::= digit+ ;
float              ::= digit '.' digit ;
digit              ::= [0-9] ;
esc_seq            ::= '\' [rnt0'"\] ;
char               ::= "'" ( esc_seq | [^\r\n\\'] ) "'" ;
string             ::= '"' ( esc_seq | [^\r\n\\""])* '"' ;
letter             ::= [a-zA-Z] ;
whitespace         ::= [ \t\r\n] ;
comment            ::= '//' [^\r\n]* [\r\n] ;
```

## Notes
- `StmtList ::= ( Stmt ';' )+ ;` - A semicolon is optional when a closing '}' is present. This allows for concise one-liners.

## Testing and changes
The grammar is also present in `light.g4` for testing and validation. Testing can be done by running `./test-grammar.sh` in this directory.

Once completed, the grammar was translated to it's current form through a mostly manual process. I did run it through https://bottlecaps.de/convert, and then undid some of the factorization and formatting.
