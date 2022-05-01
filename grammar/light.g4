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
proto           : 'fn' IDENT '(' (typed_decl (',' typed_decl)*)* ')' ('->' TYPE)?;
for_stmt        : 'for' typed_decl '=' expr ';' expr ';' NUMBER? block;
let_stmt        : 'let' typed_decl ('=' expr)?;
typed_decl      : IDENT ':' TYPE;
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
                | block
                | paren_expr
                | unop_expr;
unop_expr       : ('-' | '!') expr;
lit_expr        : NUMBER
                | BOOL;
ident_expr      : IDENT;
paren_expr      : '(' expr ')';
cond_expr       : 'if' expr block ('else' (cond_expr | block))?;

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
LETTER          : [a-zA-Z];
DIGIT           : [0-9];
WHITESPACE      : [ \t\r\n] -> skip;
COMMENT         : '//' ~[\r\n]* [\r\n] -> skip;
