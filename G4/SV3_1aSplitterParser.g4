/**
* System Verilog 3.1a Antlr 4.72 File Splitter Parser Grammar 
* Author: Alain Dargelas
* All rights reserved ACE Cloud, LLC
* 10/28/2019
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