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

lexer grammar SV3_1aPpLexer;

// A.9.2 Comments

One_line_comment : '//' Comment_text '\r'? '\n' ;

Block_comment : '/*' Comment_text '*/' ;

fragment Comment_text : .*? ;

TICK_VARIABLE : '``' [a-zA-Z0-9_]+ '``' ;

TICK_DEFINE : '`define' ;
              
TICK_CELLDEFINE : '`celldefine' ;

TICK_ENDCELLDEFINE : '`endcelldefine' ;

TICK_DEFAULT_NETTYPE : '`default_nettype' ;

TICK_UNDEF : '`undef' ;

TICK_IFDEF : '`ifdef' ;

TICK_IFNDEF : '`ifndef' ;

TICK_ELSE : '`else' ;

TICK_ELSIF : '`elsif' ;

TICK_ELSEIF : '`elseif' ;

TICK_ENDIF : '`endif' ;

TICK_INCLUDE : '`include' ;

TICK_PRAGMA : '`pragma' ;

TICK_BEGIN_KEYWORDS : '`begin_keywords' ; 

TICK_END_KEYWORDS : '`end_keywords' ;

TICK_RESETALL : '`resetall' ;

TICK_TIMESCALE : '`timescale' ;

TICK_UNCONNECTED_DRIVE : '`unconnected_drive' ;

TICK_NOUNCONNECTED_DRIVE : '`nounconnected_drive' ; 
            
TICK_LINE : '`line' ; 
 
TICK_DEFAULT_DECAY_TIME : '`default_decay_time' ;
       
TICK_DEFAULT_TRIREG_STRENGTH : '`default_trireg_strength' ;

TICK_DELAY_MODE_DISTRIBUTED : '`delay_mode_distributed' ;   
  
TICK_DELAY_MODE_PATH : '`delay_mode_path' ;          
  
TICK_DELAY_MODE_UNIT : '`delay_mode_unit' ;           
 
TICK_DELAY_MODE_ZERO : '`delay_mode_zero' ;

TICK_UNDEFINEALL : '`undefineall' ;

TICK_ACCELERATE : '`accelerate';

TICK_NOACCELERATE : '`noaccelerate';

TICK_PROTECT : '`protect' ;

TICK_USELIB : '`uselib' ;

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

TICK_FILE__ : '`__FILE__' ;   

TICK_LINE__ : '`__LINE__' ;

MODULE : 'module';

ENDMODULE : 'endmodule' ;

INTERFACE : 'interface' ;

ENDINTERFACE : 'endinterface' ;

PROGRAM : 'program' ;

ENDPROGRAM : 'endprogram' ;

PRIMITIVE : 'primivite' ;

ENDPRIMITIVE : 'endprimitive' ;

PACKAGE : 'package' ;

ENDPACKAGE : 'endpackage' ;

CHECKER : 'checker' ;

ENDCHECKER : 'endchecker' ;

CONFIG : 'config' ;

ENDCONFIG : 'endconfig' ;

Macro_identifier : '`' [a-zA-Z_] [a-zA-Z0-9_$]* ;

Macro_Escaped_identifier
    :	'`\\' ~[WS\r\t\n]*? WS
    ;

String
 : '"'                          // a opening quote
   (                            // start group
     '\\' ~('\r')        // an escaped char other than a line break char
     |                          // OR
     ~('\\' | '"'| '\r' | '\n') // any char other than '"', '\' and line breaks
   )*                           // end group and repeat zero or more times
   '"'                          // the closing quote
 ;

Simple_identifier : [a-zA-Z_] [a-zA-Z0-9_$]* ;

Spaces : (WS | TAB)+;

Pound_Pound_delay : '##' WS* [0-9] [0-9_.]*;

Pound_delay : '#' WS* [0-9] [0-9_.]*;

TIMESCALE : (WS | TAB)* [0-9]+ (WS | TAB)* ('ms' | 'us' | 'ns' | 'ps'  | 'fs' | 's' ) (WS | TAB)* '/' (WS | TAB)* [0-9]+ (WS | TAB)* ('ms' | 'us' | 'ns' | 'ps'  | 'fs' | 's')  ;

fragment
Non_zero_unsigned_number : '1'..'9' ( '_' | Decimal_digit )* ;

fragment
Decimal_number
    : Unsigned_number
    | ( Non_zero_unsigned_number WS* )? Decimal_base WS* Unsigned_number*
    | ( Non_zero_unsigned_number WS* )? Decimal_base WS* X_digit ( '_' )*
    | ( Non_zero_unsigned_number WS* )? Decimal_base WS* Z_digit ( '_' )*
    ;

/* binary_number ::= [ size ] binary_base binary_value */

fragment
Binary_number : ( Non_zero_unsigned_number WS* )? Binary_base WS* Binary_value ;

/* octal_number ::= [ size ] octal_base octal_value */

fragment
Octal_number : ( Non_zero_unsigned_number WS* )? Octal_base WS* Octal_value ;

/* hex_number ::= [ size ] hex_base hex_value */

fragment
Hex_number : ( Non_zero_unsigned_number WS* )? Hex_base WS* Hex_value ;

Number  
    :   Decimal_number 
    |   Octal_number   
    |   Binary_number  
    |   Hex_number     
    ;

/* unsigned_number <<1>> ::= decimal_digit { _ | decimal_digit } */

fragment
Unsigned_number : Decimal_digit ( '_' | Decimal_digit | ' ' )* ;

/* binary_value <<1>> ::= binary_digit { _ | binary_digit } */

fragment
Binary_value : ('_')* Binary_digit* ( ' ' | '_' | Binary_digit_no_qm )*;

/* octal_value <<1>> ::= octal_digit { _ | octal_digit } */

fragment
Octal_value : ('_')* Octal_digit* ( ' ' | '_' | Octal_digit_no_qm )*;

/* hex_value <<1>> ::= hex_digit { _ | hex_digit } */

fragment
Hex_value : ('_')* Hex_digit* ( ' ' | '_' | Hex_digit_no_qm )*;

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

fragment
Binary_digit_no_qm : X_digit | Z_digit_no_qm | ('0' | '1') ;

/* octal_digit ::= x_digit | z_digit | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 */

fragment
Octal_digit : X_digit | Z_digit | '0'..'7' ;

fragment
Octal_digit_no_qm : X_digit | Z_digit_no_qm | '0'..'7' ;

/* hex_digit ::= x_digit | z_digit | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | a | b | c | d | e | f | A | B | C | D | E | F */

fragment
Hex_digit : X_digit | Z_digit | ('0'..'9' | 'a'..'f' | 'A'..'F') ;

fragment
Hex_digit_no_qm : X_digit | Z_digit_no_qm | ('0'..'9' | 'a'..'f' | 'A'..'F') ;

/* x_digit ::= x | X */

fragment
X_digit : ('x'| 'X') ;

/* z_digit ::= z | Z | ? */

fragment
Z_digit : ('z'| 'Z' | '?')  ;

fragment
Z_digit_no_qm : ('z'| 'Z')  ;

Fixed_point_number : [0-9]+ '.' [0-9]+ ;

fragment WS : [ ]+ ;

fragment TAB : [\t]+ ;

TEXT_CR : '\\' [nr];

ESCAPED_CR : '\\' [\r\n] ; 

CR : [\r\n] ;

TICK_QUOTE : '`"' ;

TICK_BACKSLASH_TICK_QUOTE : '`\\`"' ;

TICK_TICK: '``' ; 

PARENS_OPEN : '(' ;

PARENS_CLOSE : ')' ;

COMMA : ',' ;

EQUAL_OP : '=' ;

DOUBLE_QUOTE : '"';

Escaped_identifier
    :	'\\' ~[WS\r\t\n]*? WS
    ;

CURLY_OPEN : '{' ;
CURLY_CLOSE : '}' ;
SQUARE_OPEN : '[' ;
SQUARE_CLOSE : ']' ;

Special : [~!@#$%^&*+|:;'<>.?/-]+? ;

ANY : .;
