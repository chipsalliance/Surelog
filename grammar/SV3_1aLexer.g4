/*
 Copyright 2019 Alain Dargelas

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

 http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
*/

lexer grammar SV3_1aLexer;

// ################################## TOKENS ##################################

@lexer::members {
// C++ target:
   bool sverilog;
// Java target:
// Boolean sverilog = true;
}

channels {
   WHITESPACES,
   COMMENTS
}

QMARK : '?' ;

TICK_b0 : '\'b0' ;

TICK_b1 : '\'b1' ; 

TICK_B0 : '\'B0' ; 

TICK_B1 : '\'B1' ;

TICK_0 : '\'0' ;

TICK_1 : '\'1' ;

ONE_TICK_b0 : '1\'b0' ;

ONE_TICK_b1 : '1\'b1' ;

ONE_TICK_bx : '1\'bx' ;

ONE_TICK_bX : '1\'bX' ;

ONE_TICK_B0 : '1\'B0' ;

ONE_TICK_B1 : '1\'B1' ;

ONE_TICK_Bx : '1\'Bx' ;

ONE_TICK_BX : '1\'BX' ;

Pound_Pound_delay : '##' (' ')* [0-9] [0-9_.]* ;

Pound_delay : '#' (' ')* [0-9] [0-9_.]* ;

fragment
Non_zero_unsigned_number : '1'..'9' ( '_' | Decimal_digit )* ;

fragment
Decimal_number
    : Unsigned_number
    | ( Non_zero_unsigned_number ' '* )? Decimal_base ' '* Unsigned_number
    | ( Non_zero_unsigned_number ' '* )? Decimal_base ' '* X_digit ( '_' )*
    | ( Non_zero_unsigned_number ' '* )? Decimal_base ' '* Z_digit ( '_' )*
    ;

/* binary_number ::= [ size ] binary_base binary_value */

fragment
Binary_number : ( Non_zero_unsigned_number ' '* )? Binary_base ' '* Binary_value ;

/* octal_number ::= [ size ] octal_base octal_value */

fragment
Octal_number : ( Non_zero_unsigned_number ' '* )? Octal_base ' '* Octal_value ;

/* hex_number ::= [ size ] hex_base hex_value */

fragment
Hex_number : ( Non_zero_unsigned_number ' '* )? Hex_base ' '* Hex_value ;

Integral_number  
    :   Decimal_number 
    |   Octal_number   
    |   Binary_number  
    |   Hex_number     
    ;

/* real_number ::=
fixed_point_number
| unsigned_number [ . unsigned_number ] exp [ sign ] unsigned_number */

Real_number
    :   Fixed_point_number
    |   Unsigned_number ( '.' Unsigned_number )? ('e'|'E') ( PLUS | MINUS )? Unsigned_number
    ;

/* fixed_point_number <<1>> ::= unsigned_number . unsigned_number */

fragment
Fixed_point_number : Unsigned_number DOT Unsigned_number ;

/* unsigned_number <<1>> ::= decimal_digit { _ | decimal_digit } */

fragment
Unsigned_number : Decimal_digit ( '_' | Decimal_digit )* ;

/* binary_value <<1>> ::= binary_digit { _ | binary_digit } */

fragment
Binary_value : ('_')* Binary_digit ( '_' | Binary_digit )* ;

/* octal_value <<1>> ::= octal_digit { _ | octal_digit } */

fragment
Octal_value : ('_')* Octal_digit ( '_' | Octal_digit )* ;

/* hex_value <<1>> ::= hex_digit { _ | hex_digit } */

fragment
Hex_value : ('_')* Hex_digit ( '_' | Hex_digit )* ;

/* decimal_base <<1>> ::= [s|S]d | [s|S]D */

fragment
Decimal_base : '\'' ('s' | 'S')? ('d' | 'D') ;

/* binary_base <<1>> ::= [s|S]b | [s|S]B */

fragment
Binary_base : '\'' ('s' | 'S')? ('b' | 'B') ;

/* octal_base <<1>> ::= [s|S]o | [s|S]O */

fragment
Octal_base : '\'' ('s' | 'S')? ( 'o' | 'O') ;

/* hex_base <<1>> ::ps [s|S]h | [s|S]H */

fragment
Hex_base : '\'' ('s' | 'S')?  ('h' | 'H') ;


/* decimal_digit ::= 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 */

fragment
Decimal_digit : '0'..'9' ;

/* binary_digit ::= x_digit | z_digit | 0 | 1 */

fragment
Binary_digit : X_digit | Z_digit | ('0' | '1') ;

/* octal_digit ::= x_digit | z_digit | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 */

fragment
Octal_digit : X_digit | Z_digit | '0'..'7' ;

/* hex_digit ::= x_digit | z_digit | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | a | b | c | d | e | f | A | B | C | D | E | F */

fragment
Hex_digit : X_digit | Z_digit | ('0'..'9' | 'a'..'f' | 'A'..'F') ;

/* x_digit ::= x | X */

fragment
X_digit : ('x'| 'X') ;

/* z_digit ::= z | Z | ? */

fragment
Z_digit : ('z'| 'Z' | QMARK)  ;

/* edge_descriptor */

/* z_or_x ::= x | X | z | Z */

// A.8.8 Strings

String
 : '"'                          // a opening quote
   (                            // start group
     '\\' ~('\r')        // an escaped char other than a line break char
     |                          // OR
     ~('\\' | '"'| '\r' | '\n') // any char other than '"', '\' and line breaks
   )*                           // end group and repeat zero or more times
   '"'                          // the closing quote
 ;

// A.9.2 Comments

/* one_line_comment ::= // comment_text \n */

One_line_comment : '//' Comment_text '\r'? ('\n' | EOF) -> channel(COMMENTS);

// block_comment ::= /* comment_text */ 

Block_comment : '/*' Comment_text '*/' -> channel(COMMENTS);

/* comment_text ::= { Any_ASCII_character } */

fragment Comment_text : .*? ;

ASSOCIATIVE_UNSPECIFIED : '[' [ ]* '*' [ ]* ']' ;

ATSTAR : '@' ' '? '*' ;

AT_PARENS_STAR : '@' ' '? '(' ' '? '*' ' '? ')' ;

// 9.4 White space

White_space : [ \t\n\r]+ -> channel(WHITESPACES) ;

// ######################### LEXER RULES ################################

INCLUDE : 'include';
    
LIBRARY : 'library' ;

INCDIR : '-incdir' ;
 
COMMA : ',' ;
 
SEMICOLUMN : ';' ;

COLUMNCOLUMN : '::' ;

COLUMN : ':' ;

DESIGN : 'design' ;

DOT : '.' ;

DEFAULT : 'default' ;

INSTANCE : 'instance' ;

CELL : 'cell' ;

LIBLIST : 'liblist' ;

USE : 'use' ;

MODULE : 'module';

ENDMODULE : 'endmodule' ;
         
OPEN_PARENS : '(' ;

CLOSE_PARENS : ')' ;

STAR : '*' ;

EXTERN : 'extern' ;

MACROMODULE : 'macromodule' ;

INTERFACE : 'interface' ;

ENDINTERFACE : 'endinterface' ;

PROGRAM : 'program' ;

ENDPROGRAM : 'endprogram' ;

VIRTUAL : 'virtual' ; 

CLASS : 'class' ; 

ENDCLASS : 'endclass' ;

EXTENDS : 'extends' ;

PACKAGE : 'package' ;

ENDPACKAGE : 'endpackage' ;

TIMEUNIT : 'timeunit' ;

TIMEPRECISION : 'timeprecision' ;

CHECKER : 'checker' ;

ENDCHECKER : 'endchecker' ;

CONFIG : 'config' ;

ENDCONFIG : 'endconfig' ;

TYPE : 'type' { sverilog }?;

UNTYPED : 'untyped' ;

INPUT : 'input' ;

OUTPUT : 'output' ;

INOUT : 'inout' ;

REF : 'ref' { sverilog }?;

CLOCKING : 'clocking' ;

DEFPARAM : 'defparam' ;

BIND : 'bind' ;

FORKJOIN : 'forkjoin' ;

CONST : 'const' ;

FUNCTION : 'function' ;

NEW : 'new' { sverilog }?;

STATIC : 'static' ;
         
PROTECTED : 'protected' ;

LOCAL : 'local' ;

RAND : 'rand' ;

RANDC : 'randc' ;

SUPER : 'super' ;

ENDFUNCTION : 'endfunction' ;

CONSTRAINT : 'constraint' ;

OPEN_CURLY : '{' ;

CLOSE_CURLY : '}' ;
 
SOLVE : 'solve' ;
 
BEFORE : 'before' ;

IMPLY : '->' ;

IF : 'if' ;

ELSE : 'else';

FOREACH : 'foreach' ;

ASSIGN_VALUE : ':=' ;

/* Replaced by COLUMN DIV :  ASSIGN_RANGE : ':/' ; */

AUTOMATIC : 'automatic' ;

LOCALPARAM : 'localparam' ;

PARAMETER : 'parameter' ;

SPECPARAM : 'specparam' ;

IMPORT : 'import' ; 

GENVAR : 'genvar' ;

VECTORED : 'vectored' ;

SCALARED : 'scalared' ;

TYPEDEF : 'typedef' ;

ENUM : 'enum';

STRUCT : 'struct' ;

UNION : 'union' ;

PACKED : 'packed' ;

STRING : 'string' ;
 
CHANDLE : 'chandle' ;
 
EVENT : 'event' ;

OPEN_BRACKET : '[' ;

CLOSE_BRACKET : ']' ;

BYTE : 'byte' { sverilog }?;

SHORTINT : 'shortint'; 

INT : 'int' ;

LONGINT : 'longint' ;

INTEGER : 'integer' ;

TIME : 'time' ;

BIT : 'bit' { sverilog }?;

LOGIC : 'logic' { sverilog }?;

REG : 'reg' ;
       
SHORTREAL : 'shortreal' ;
 
REAL : 'real' ;

REALTIME : 'realtime' ;

NEXTTIME : 'nexttime' ;

S_NEXTTIME : 's_nexttime' ;

S_ALWAYS : 's_always' ;

UNTIL_WITH : 'until_with' ;

S_UNTIL_WITH : 's_until_with';

ACCEPT_ON      : 'accept_on' ;

REJECT_ON      : 'reject_on' ;

SYNC_ACCEPT_ON : 'sync_accept_on' ;

SYNC_REJECT_ON : 'sync_reject_on' ;

EVENTUALLY : 'eventually' ;

S_EVENTUALLY : 's_eventually' ;

SUPPLY0 : 'supply0' ;
 
SUPPLY1 : 'supply1' ;

TRI : 'tri' ;

TRIAND : 'triand' ;

TRIOR : 'trior' ;

TRI0 : 'tri0' ;

TRI1 : 'tri1' ;

WIRE : 'wire' ;

UWIRE : 'uwire' ;

WAND : 'wand' ;

WOR : 'wor' ;

TRIREG : 'trireg' ;

SIGNED : 'signed';
 
UNSIGNED : 'unsigned';

INTERCONNECT : 'interconnect' ;

VAR : 'var' { sverilog }?;

VOID : 'void' ;

HIGHZ0 : 'highz0' ;
    
HIGHZ1 : 'highz1' ;

STRONG : 'strong' ;

WEAK : 'weak' ;

STRONG0 : 'strong0' ;

PULL0 : 'pull0' ;

WEAK0 : 'weak0' ;

STRONG1 : 'strong1' ;

PULL1 : 'pull1' ;

WEAK1 : 'weak1' ;

SMALL : '(small)';

MEDIUM : '(medium)' ;

LARGE : '(large)' ;

PATHPULSE : 'PATHPULSE' ;

DOLLAR : '$' ;

EXPORT : 'export' ;

CONTEXT : 'context' { sverilog }?;

PURE : 'pure' ;

IMPLEMENTS : 'implements' ;

ENDTASK : 'endtask' ;

PLUSPLUS : '++' ;

PLUS : '+' ;

MINUSMINUS : '--' ;

MINUS : '-' ;

STARCOLUMNCOLUMNSTAR : '*::*' ;

STARSTAR : '**' ;

DIV : '/' ;

PERCENT : '%' ;

EQUIV : '==' ;

NOTEQUAL : '!=' ;

LESS : '<' ;

LESS_EQUAL : '<=' ; 

GREATER : '>' ;

EQUIVALENCE : '<->' ;

GREATER_EQUAL : '>=' ;

MODPORT : 'modport' ;

DOLLAR_UNIT : DOLLAR 'unit' ;

OPEN_PARENS_STAR : '(*' ;

STAR_CLOSE_PARENS : '*)' ;

ASSERT : 'assert' ; 

PROPERTY : 'property' ;

ASSUME : 'assume' ;

COVER : 'cover' ;

EXPECT : 'expect' { sverilog }?;

ENDPROPERTY : 'endproperty' ;

DISABLE : 'disable' ;

IFF : 'iff' ;

OVERLAP_IMPLY : '|->' ;               

NON_OVERLAP_IMPLY : '|=>' ;

NOT : 'not' ;
 
OR : 'or' ;

AND : 'and' ;

SEQUENCE : 'sequence' ;

ENDSEQUENCE : 'endsequence' ;

INTERSECT : 'intersect' ;

FIRST_MATCH : 'first_match' ;
 
THROUGHOUT : 'throughout' ;

WITHIN : 'within' ;

POUNDPOUND : '##' ;

OVERLAPPED : '#-#' ;

NONOVERLAPPED : '#=#' ;

POUND : '#' ;

CONSECUTIVE_REP : '[*' ;

NON_CONSECUTIVE_REP : '[=' ;

GOTO_REP : '[->' ;

DIST : 'dist' ;

COVERGROUP : 'covergroup' ;
    
ENDGROUP : 'endgroup' ;

OPTION_DOT : 'option' DOT;
 
TYPE_OPTION_DOT : 'type_option' DOT;

ATAT : '@@' ;

BEGIN : 'begin' ;

END : 'end' ;

WILDCARD : 'wildcard' ;

BINS : 'bins';

ILLEGAL_BINS : 'illegal_bins' ;

IGNORE_BINS : 'ignore_bins' ;

TRANSITION_OP : '=>' ;

BANG : '!' ;

SOFT : 'soft' { sverilog }?;

UNTIL : 'until' ;

S_UNTIL : 's_until' ;

IMPLIES : 'implies' ;

LOGICAL_AND : '&&' ;

LOGICAL_OR : '||' ;

BINSOF : 'binsof' ;

PULLDOWN : 'pulldown' ;

PULLUP : 'pullup' ;

CMOS : 'cmos' ;

RCMOS : 'rcmos' ;

BUFIF0 : 'bufif0' ;
           
BUFIF1 : 'bufif1' ;

NOTIF0 : 'notif0' ;

NOTIF1 : 'notif1' ;

NMOS : 'nmos' ; 

PMOS : 'pmos' ; 

RNMOS : 'rnmos' ; 

RPMOS  : 'rpmos' ;

NAND : 'nand' ;

NOR  : 'nor' ;

XOR  : 'xor' ;

XNOR : 'xnor' ;

BUF  : 'buf' ;

TRANIF0  : 'tranif0' ;

TRANIF1  : 'tranif1' ;

RTRANIF1  : 'rtranif1' ;

RTRANIF0  : 'rtranif0' ;

TRAN  : 'tran' ;

RTRAN : 'rtran' ;

DOTSTAR : '.*' ;

GENERATE : 'generate' ;
 
ENDGENERATE : 'endgenerate' ;

CASE : 'case' ;

ENDCASE : 'endcase' ;

FOR : 'for' ;

GLOBAL : 'global' { sverilog }?;

PRIMITIVE : 'primitive' ;

ENDPRIMITIVE : 'endprimitive' ;

TABLE : 'table' ;

ENDTABLE : 'endtable' ;

INITIAL : 'initial' ;

ASSIGN : 'assign' ;

ALIAS : 'alias' ;
 
ALWAYS : 'always' ;

ALWAYS_COMB : 'always_comb' ;

ALWAYS_LATCH : 'always_latch' ;

ALWAYS_FF : 'always_ff' ;
 
ADD_ASSIGN : '+=' ;

SUB_ASSIGN : '-=' ;

MULT_ASSIGN : '*=' ;

DIV_ASSIGN : '/=' ;

MODULO_ASSIGN : '%=' ;

BITW_AND_ASSIGN : '&=' ;

BITW_OR_ASSIGN : '|=' ;

BITW_XOR_ASSIGN : '^=' ;

BITW_LEFT_SHIFT_ASSIGN : '<<=' ;

BITW_RIGHT_SHIFT_ASSIGN : '>>=' ;

DEASSIGN : 'deassign' ;

FORCE : 'force' ;

RELEASE : 'release' ;

FORK : 'fork' ;

JOIN : 'join' ;

JOIN_ANY : 'join_any' ;

JOIN_NONE : 'join_none' ;

REPEAT : 'repeat' ;

AT : '@' ;

RETURN : 'return' ;

BREAK : 'break' ;

CONTINUE : 'continue' ;

WAIT : 'wait' ;

WAIT_ORDER : 'wait_order' ;

UNIQUE : 'unique' ; 

UNIQUE0 : 'unique0' ; 

PRIORITY : 'priority' ;

MATCHES : 'matches' ;

CASEZ : 'casez' ;

CASEX : 'casex' ;

RANDCASE : 'randcase' ;

TAGGED : 'tagged' ;

FOREVER : 'forever' ;

WHILE : 'while' ;

DO : 'do' { sverilog }?;

RESTRICT : 'restrict' ;

LET : 'let' ;

TICK : '\'';

ENDCLOCKING : 'endclocking' ;

RANDSEQUENCE : 'randsequence' ;

SHIFT_RIGHT : '>>' ;

SHIFT_LEFT : '<<' ;

WITH : 'with' ;

INC_PART_SELECT_OP : '+:' ;

DEC_PART_SELECT_OP : '-:' ;

INSIDE : 'inside' ;

NULL_KEYWORD : 'null' ;

THIS : 'this' { sverilog }?;
          
DOLLAR_ROOT : DOLLAR 'root' ;

RANDOMIZE : 'randomize' { sverilog }?;

FINAL : 'final' { sverilog }?;

TASK : 'task' ;

COVERPOINT : 'coverpoint' ;

CROSS : 'cross' ;

POSEDGE : 'posedge' ;
            
NEGEDGE : 'negedge' ;

SPECIFY : 'specify' ;

ENDSPECIFY : 'endspecify' ;

PULSESTYLE_ONEVENT : 'pulsestyle_onevent' ;

PULSESTYLE_ONDETECT : 'pulsestyle_ondetect' ;

SHOWCANCELLED : 'showcancelled' ;

NOSHOWCANCELLED : 'noshowcancelled' ;

IFNONE : 'ifnone' ;

SAMPLE : 'sample' { sverilog }?;

EDGE : 'edge' ;

NON_BLOCKING_TRIGGER_EVENT_OP : '->>' ;

ARITH_SHIFT_RIGHT : '>>>' ;

ARITH_SHIFT_LEFT : '<<<' ;

ARITH_SHIFT_LEFT_ASSIGN : '<<<=' ;

ARITH_SHIFT_RIGHT_ASSIGN : '>>>=' ;

FOUR_STATE_LOGIC_EQUAL : '===' ;
    
FOUR_STATE_LOGIC_NOTEQUAL : '!==' ;

BINARY_WILDCARD_EQUAL : '==?' ;

BINARY_WILDCARD_NOTEQUAL : '!=?' ;

FULL_CONN_OP : '*>' ;

COND_PRED_OP : '&&&' ;

BITW_AND : '&' ;

BITW_OR : '|' ;

REDUCTION_NOR : '~|' ;

REDUCTION_NAND : '~&' ;

REDUCTION_XNOR1 : '^~' ;

WILD_EQUAL_OP : '=?=' ;

WILD_NOTEQUAL_OP : '!?=' ;

ASSIGN_OP : '=' ;

NETTYPE : 'nettype' ;

// A.9.3 Identifiers

/* escaped_identifier ::= \ {any_ASCII_character_except_white_space} white_space */
/* Example: \`~!-_=+\|[]{};:'"",./<>? */

//Escaped_identifier : '^^^' [\\|+a-zA-Z0-9_$:,-/*{}()`~!=;'"<>?.]* '^^^' ;

Escaped_identifier : '#~@' .*? '#~@' ;

TILDA : '~' ;

BITW_XOR : '^';

REDUCTION_XNOR2 : '~^' ;

/* simple_identifier <<2>> ::= [ a-zA-Z_ ] { [ a-zA-Z0-9_$ ] } */

Simple_identifier : [a-zA-Z_] [a-zA-Z0-9_$]* ;

TICK_LINE : '`line' ;

TICK_TIMESCALE : '`timescale' ;

TICK_BEGIN_KEYWORDS : '`begin_keywords' ; 

TICK_END_KEYWORDS : '`end_keywords' ;

TICK_UNCONNECTED_DRIVE : '`unconnected_drive' ;

TICK_NOUNCONNECTED_DRIVE : '`nounconnected_drive' ;

TICK_CELLDEFINE : '`celldefine' ;

TICK_ENDCELLDEFINE : '`endcelldefine' ;

TICK_DEFAULT_NETTYPE : '`default_nettype' ;

TICK_DEFAULT_DECAY_TIME : '`default_decay_time' ;
       
TICK_DEFAULT_TRIREG_STRENGTH : '`default_trireg_strength' ;

TICK_DELAY_MODE_DISTRIBUTED : '`delay_mode_distributed' ;   
  
TICK_DELAY_MODE_PATH : '`delay_mode_path' ;          
  
TICK_DELAY_MODE_UNIT : '`delay_mode_unit' ;           
 
TICK_DELAY_MODE_ZERO : '`delay_mode_zero' ;

TICK_ACCELERATE : '`accelerate';

TICK_NOACCELERATE : '`noaccelerate';

TICK_PROTECT : '`protect' ;

TICK_DISABLE_PORTFAULTS : '`disable_portfaults' ;

TICK_ENABLE_PORTFAULTS : '`enable_portfaults' ;

TICK_NOSUPPRESS_FAULTS : '`nosuppress_faults' ;

TICK_SUPPRESS_FAULTS : '`suppress_faults' ;

TICK_SIGNED : '`signed' ;

TICK_UNSIGNED : '`unsigned' ; 

TICK_ENDPROTECT : '`endprotect' ; 

TICK_PROTECTED : '`protected' ;

TICK_ENDPROTECTED : '`endprotected' ; 

TICK_EXPAND_VECTORNETS : '`expand_vectornets' ;

TICK_NOEXPAND_VECTORNETS : '`noexpand_vectornets' ;

TICK_AUTOEXPAND_VECTORNETS : '`autoexpand_vectornets' ;

TICK_REMOVE_GATENAME : '`remove_gatename' ;

TICK_NOREMOVE_GATENAMES : '`noremove_gatenames' ;

TICK_REMOVE_NETNAME : '`remove_netname' ;

TICK_NOREMOVE_NETNAMES : '`noremove_netnames' ; 

ONESTEP : '1step' ;

TICK_USELIB : '`uselib' ;

TICK_PRAGMA : '`pragma' ;

BACK_TICK : '`' ;

SURELOG_MACRO_NOT_DEFINED : 'SURELOG_MACRO_NOT_DEFINED:' Simple_identifier '!!!' ;

