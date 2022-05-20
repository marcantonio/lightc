grammar light;

program         : stmt_list;
stmt_list       : (stmt ';')+;
stmt            : let_stmt
                | for_stmt
                | fn_decl
                | extern_decl
                | expr;
block           : '{' stmt_list? '}';
fn_decl         : proto block;
extern_decl     : 'extern' proto;
proto           : 'fn' IDENT '(' (typed_decl (',' typed_decl)*)* ')' ('->' type_antn)?;
for_stmt        : 'for' typed_decl '=' expr ';' expr ';' NUMBER? block;
let_stmt        : 'let' typed_decl ('=' expr)?;
typed_decl      : IDENT ':' type_antn;
type_antn       : TYPE
                | '[' TYPE ']';
expr            : primary_expr
                | expr ('*' | '/') expr
                | expr ('+' | '-') expr
                | expr ('>' | '<' | '==') expr
                | expr '&&' expr
                | expr '||' expr
                | ident_expr '=' expr;
primary_expr    : cond_expr
                | lit_expr
                | ident_expr
                | call_expr
                | block
                | paren_expr
                | unop_expr
                | primary_expr index ;
unop_expr       : ('-' | '!') expr;
lit_expr        : NUMBER
                | BOOL
                | char_lit
                | array_lit;
call_expr       : IDENT '(' expr_list? ')';
paren_expr      : '(' expr ')';
cond_expr       : 'if' expr block ('else' (cond_expr | block))?;
ident_expr      : IDENT;
index           : '[' expr ']';
array_lit       : '[' expr_list? ']';
char_lit        : CHAR;
expr_list       : expr ','? | expr (',' expr)*;

TYPE            : 'int'
                | 'int8 '
                | 'int16'
            	| 'int32'
            	| 'int64'
            	| 'uint'
            	| 'uint8'
            	| 'uint16'
            	| 'uint32'
            	| 'uint64'
            	| 'float'
                | 'double'
                | 'bool'
                | 'char';
BOOL            : 'true' | 'false';
IDENT           : LETTER (LETTER | DIGIT | '_')*;
NUMBER          : INTEGER | FLOAT;
INTEGER         : DIGIT+;
FLOAT           : DIGIT '.' DIGIT;
DIGIT           : [0-9];
CHAR            : '\'' (~['\\\r\n\t] | '\\' [n0]) '\'';
LETTER          : [a-zA-Z];
WHITESPACE      : [ \t\r\n] -> skip;
COMMENT         : '//' ~[\r\n]* [\r\n] -> skip;
