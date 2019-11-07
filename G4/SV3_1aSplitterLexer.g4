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

lexer grammar SV3_1aSplitterLexer;

// A.9.2 Comments

One_line_comment : '//' Comment_text '\r'? '\n' ;

Block_comment : '/*' Comment_text '*/' ;

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
