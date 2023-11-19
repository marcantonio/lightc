// For the official grammar, see grammar.md. This is just for testing and validation
grammar light;

program              : mod_decl? stmt_list;
stmt_list            : (stmt ';')+;
stmt                 : let_stmt
                     | for_stmt
                     | loop_stmt
                     | while_stmt
                     | fn_decl
                     | extern_decl
                     | struct_decl
                     | use_stmt
                     | break_stmt
                     | next_stmt
                     | expr;
mod_decl             : 'module' IDENT ';';
block                : '{' stmt_list? '}';
fn_decl              : proto block;
extern_decl          : 'extern' proto;
struct_decl          : 'struct' IDENT '{' (let_stmt ';' | fn_decl ';')* '}' ;
proto                : 'fn' IDENT '(' (typed_decl (',' typed_decl)*)* ')' ('->' type_antn)?;
for_stmt             : 'for' var_init ';' expr ';' NUMBER? block;
loop_stmt            : 'loop' block;
while_stmt           : 'while' expr block;
let_stmt             : 'let' var_init;
var_init             : typed_decl ('=' expr)?;
typed_decl           : IDENT ':' type_antn;
type_antn            : TYPE
                     | '[' TYPE ']';
use_stmt             : 'use' IDENT ;
break_stmt           : 'break' ;
next_stmt            : 'next' ;
expr                 : primary_expr
                     | expr ('*' | '/') expr
                     | expr ('+' | '-') expr
                     | expr ('>' | '>=' | '<' | '<=') expr
                     | expr ('==' | '!=') expr
                     | expr ('&' | '|' | '^') expr
                     | expr '&&' expr
                     | expr '||' expr
                     | assignable_expr ('=' | '+=' | '-=') expr;
primary_expr         : cond_expr
                     | self_expr
                     | lit_expr
                     | ident_expr
                     | call_expr
                     | block
                     | paren_expr
                     | unop_expr
                     | primary_expr '[' expr ']'
                     | primary_expr '.' (ident_expr | call_expr);
// ANTLR doesn't do mutual left recursion, so some expressions are defined as directly
// recursive above. The Light parser handles this properly.
//                   | index_expr
//                   | field_selector_expr;
//                   | method_selector_expr;
index_expr           : primary_expr '[' expr ']';
field_selector_expr  : primary_expr '.' ident_expr;
self_expr            : 'self' '.' (ident_expr | call_expr);
assignable_expr      : ident_expr | index_expr | self_expr | field_selector_expr;
unop_expr            : ('-' | '!') expr;
lit_expr             : NUMBER
                     | BOOL
                     | char_lit
                     | array_lit;
call_expr            : IDENT '(' expr_list? ')';
paren_expr           : '(' expr ')';
cond_expr            : 'if' expr block ('else' (cond_expr | block))?;
ident_expr           : IDENT;
array_lit            : '[' expr_list? ']';
char_lit             : CHAR;
expr_list            : expr ','? | expr (',' expr)*;

TYPE                 : 'int'
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
BOOL                 : 'true' | 'false';
IDENT                : LETTER (LETTER | DIGIT | '_' | '::')*;
NUMBER               : INTEGER | FLOAT;
INTEGER              : DIGIT+;
FLOAT                : DIGIT '.' DIGIT;
DIGIT                : [0-9];
CHAR                 : '\'' (~['\\\r\n\t] | '\\' [n0]) '\'';
LETTER               : [a-zA-Z];
WHITESPACE           : [ \t\r\n] -> skip;
COMMENT              : '//' ~[\r\n]* [\r\n] -> skip;
