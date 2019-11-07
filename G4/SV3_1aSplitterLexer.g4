/**
* System Verilog 3.1a Antlr 4.72 File Splitter Lexer Grammar 
* Author: Alain Dargelas
* All rights reserved ACE Cloud, LLC
* 10/28/2019
*/
lexer grammar SV3_1aSplitterLexer;

// A.9.2 Comments

/* one_line_comment ::= // comment_text \n */

One_line_comment : '//' Comment_text '\r'? '\n' ;

// block_comment ::= /* comment_text */ 

Block_comment : '/*' Comment_text '*/' ;

/* comment_text ::= { Any_ASCII_character } */

fragment Comment_text : (WS | CR | TAB)* | .*? ;

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
 
String
 : '"'                          // a opening quote
   (                            // start group
     '\\' ~('\r')        // an escaped char other than a line break char
     |                          // OR
     ~('\\' | '"'| '\r' | '\n') // any char other than '"', '\' and line breaks
   )*                           // end group and repeat zero or more times
   '"'                          // the closing quote
 ;

Spaces : (WS | TAB)+;



fragment WS : [ ]+ ;

fragment TAB : [\t]+ ;

CR : [\r\n] ;


ANY : .;
