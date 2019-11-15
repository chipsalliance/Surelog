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

parser grammar SV3_1aSplitterParser;


options { tokenVocab = SV3_1aSplitterLexer; }

source_text : ( description ) *;

description :
	      module 
	    | endmodule
	    | sv_interface 
	    | endinterface 
	    | program 
	    | endprogram 
	    | primitive 
	    | endprimitive 
	    | sv_package 
	    | endpackage
	    | checker
	    | endchecker 
	    | config 
	    | endconfig
	    | ANY
	    ;


module : MODULE ;
endmodule : ENDMODULE  ;

sv_interface : INTERFACE  ;
endinterface : ENDINTERFACE  ;

program : PROGRAM  ;
endprogram : ENDPROGRAM  ;

primitive : PRIMITIVE ;
endprimitive : ENDPRIMITIVE ;

sv_package : PACKAGE  ;
endpackage : ENDPACKAGE  ;

checker : CHECKER ;
endchecker : ENDCHECKER ;

config : CONFIG ;
endconfig : ENDCONFIG ;

any : ANY ;