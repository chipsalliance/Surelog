/**
* System Verilog 3.1a Antlr 4.0 Pre Processor Parser Grammar 
* Author: Alain Dargelas
* All rights reserved ACE Cloud, LLC
* 02/12/2017
*/
parser grammar SV3_1aPpParser;


options { tokenVocab = SV3_1aPpLexer; }

source_text : ( description ) *;

description :
            unterminated_string
	    | string
	    | number
            | macro_definition
	    | comments 
            | celldefine_directive_one_line 
            | endcelldefine_directive_one_line
            | default_nettype_directive_one_line
            | undef_directive
            | ifdef_directive_one_line 
            | ifndef_directive_one_line
            | else_directive_one_line 
            | elsif_directive_one_line
	    | elseif_directive_one_line
            | endif_directive_one_line 
            | include_directive_one_line
            | include_directive
            | resetall_directive_one_line
	    | begin_keywords_directive_one_line
	    | begin_keywords_directive
	    | end_keywords_directive_one_line
            | timescale_directive_one_line
            | unconnected_drive_directive_one_line
            | nounconnected_drive_directive_one_line 
            | line_directive_one_line
            | default_decay_time_directive_one_line
            | default_trireg_strenght_directive_one_line
            | delay_mode_distributed_directive_one_line   
            | delay_mode_path_directive_one_line   
            | delay_mode_unit_directive_one_line         
            | delay_mode_zero_directive_one_line
	    | protect_directive_one_line 
	    | endprotect_directive_one_line 
	    | protected_directive_one_line 
	    | endprotected_directive_one_line 
	    | expand_vectornets_directive_one_line 
	    | noexpand_vectornets_directive_one_line 
	    | autoexpand_vectornets_directive_one_line
	    | remove_gatename_directive_one_line 
	    | noremove_gatenames_directive_one_line 
	    | remove_netname_directive_one_line 
 	    | noremove_netnames_directive_one_line
	    | accelerate_directive_one_line
	    | noaccelerate_directive_one_line
            | undefineall_directive
	    | uselib_directive_one_line
	    | disable_portfaults_directive_one_line
	    | enable_portfaults_directive_one_line 
	    | nosuppress_faults_directive_one_line 
	    | suppress_faults_directive_one_line 
	    | signed_directive_one_line 
	    | unsigned_directive_one_line
	    | pragma_directive_one_line
            | sv_file_directive 
            | sv_line_directive
	    | macro_instance
	    | module 
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
	    | text_blob
	    | escaped_identifier
	    | pound_delay
	    ;

macro_instance : (Macro_identifier | Macro_Escaped_identifier) Spaces* PARENS_OPEN macro_actual_args PARENS_CLOSE # MacroInstanceWithArgs
	       | (Macro_identifier | Macro_Escaped_identifier)                                                    # MacroInstanceNoArgs
	       ;

unterminated_string : DOUBLE_QUOTE (string_blob)* CR;

macro_actual_args : (macro_arg)* (COMMA macro_arg)* ;

comments :    One_line_comment 
	    | Block_comment 
	    ;

number : Number ;

pound_delay : Pound_delay ;

macro_definition :
              define_directive
	    | multiline_args_macro_definition
	    | simple_no_args_macro_definition	    
            | multiline_no_args_macro_definition
	    | simple_args_macro_definition	
	    ;

include_directive_one_line : include_directive Spaces* CR;
include_directive : TICK_INCLUDE Spaces (String | Simple_identifier | Escaped_identifier | macro_instance);

line_directive_one_line : line_directive Spaces* CR ;
line_directive : TICK_LINE Spaces number String Spaces number;

default_nettype_directive_one_line : default_nettype_directive Spaces* CR ;
default_nettype_directive : TICK_DEFAULT_NETTYPE Spaces Simple_identifier;

sv_file_directive : TICK_FILE__ ;

sv_line_directive : TICK_LINE__ ;

timescale_directive_one_line : timescale_directive Spaces* CR ;
timescale_directive : TICK_TIMESCALE TIMESCALE ;

undef_directive : TICK_UNDEF Spaces (Simple_identifier | Escaped_identifier | macro_instance);

ifdef_directive_one_line : ifdef_directive Spaces* (
                              (One_line_comment | CR )
                            | (description* ((else_directive | elseif_directive | elsif_directive )? description+)* endif_directive)
                           );

ifdef_directive : TICK_IFDEF Spaces (Simple_identifier | Escaped_identifier | macro_instance) ;
ifdef_directive_in_macro_body : TICK_IFDEF Spaces (identifier_in_macro_body | Escaped_identifier | macro_instance) ;

ifndef_directive_one_line : ifndef_directive Spaces* (
                              (One_line_comment | CR )
                            | (description* ((else_directive | elseif_directive | elsif_directive )? description+)* endif_directive)
                           );

ifndef_directive : TICK_IFNDEF Spaces (Simple_identifier | Escaped_identifier | macro_instance);
ifndef_directive_in_macro_body : TICK_IFNDEF Spaces (identifier_in_macro_body | Escaped_identifier | macro_instance);

elsif_directive_one_line : elsif_directive Spaces* (One_line_comment | CR ) ;
elsif_directive : TICK_ELSIF Spaces (Simple_identifier | Escaped_identifier | macro_instance);
elsif_directive_in_macro_body : TICK_ELSIF Spaces (identifier_in_macro_body | Escaped_identifier | macro_instance);

elseif_directive_one_line : elseif_directive Spaces* (One_line_comment | CR ) ;
elseif_directive : TICK_ELSEIF Spaces (Simple_identifier | Escaped_identifier | macro_instance);
elseif_directive_in_macro_body : TICK_ELSEIF Spaces (identifier_in_macro_body | Escaped_identifier | macro_instance);

else_directive_one_line : else_directive Spaces* (One_line_comment | CR );
else_directive : TICK_ELSE;

endif_directive_one_line : TICK_ENDIF Spaces* One_line_comment 
	 	         | TICK_ENDIF Spaces* CR
	    	         | TICK_ENDIF EOF;
			 
endif_directive : TICK_ENDIF Spaces* One_line_comment
		| TICK_ENDIF ;

resetall_directive_one_line : resetall_directive Spaces* CR ;  
resetall_directive : TICK_RESETALL;  

begin_keywords_directive_one_line : begin_keywords_directive Spaces* CR ;  
begin_keywords_directive : TICK_BEGIN_KEYWORDS Spaces String;

end_keywords_directive_one_line : end_keywords_directive Spaces* CR ;  
end_keywords_directive : TICK_END_KEYWORDS;

pragma_directive_one_line : pragma_directive Spaces* CR ;
pragma_directive : TICK_PRAGMA Spaces Simple_identifier ( pragma_expression ( Special pragma_expression )* )* ;

celldefine_directive_one_line : celldefine_directive Spaces* CR ;
celldefine_directive : TICK_CELLDEFINE ;

endcelldefine_directive_one_line : endcelldefine_directive Spaces* CR ;
endcelldefine_directive : TICK_ENDCELLDEFINE;

protect_directive_one_line : protect_directive Spaces* CR ;
protect_directive : TICK_PROTECT;

endprotect_directive_one_line : endprotect_directive Spaces* CR ; 
endprotect_directive : TICK_ENDPROTECT; 

protected_directive_one_line : protected_directive Spaces* CR ;
protected_directive : TICK_PROTECTED;

endprotected_directive_one_line : endprotected_directive Spaces* CR ; 
endprotected_directive : TICK_ENDPROTECTED; 

expand_vectornets_directive_one_line : expand_vectornets_directive Spaces* CR ;
expand_vectornets_directive : TICK_EXPAND_VECTORNETS ;

noexpand_vectornets_directive_one_line : noexpand_vectornets_directive Spaces* CR ;
noexpand_vectornets_directive : TICK_NOEXPAND_VECTORNETS;

autoexpand_vectornets_directive_one_line : autoexpand_vectornets_directive Spaces* CR ;
autoexpand_vectornets_directive : TICK_AUTOEXPAND_VECTORNETS;

uselib_directive_one_line : uselib_directive CR ;
uselib_directive : TICK_USELIB ( text_blob )+;

disable_portfaults_directive_one_line : disable_portfaults_directive Spaces* CR  ;
disable_portfaults_directive : TICK_DISABLE_PORTFAULTS;

enable_portfaults_directive_one_line : enable_portfaults_directive Spaces* CR  ;
enable_portfaults_directive : TICK_ENABLE_PORTFAULTS;

nosuppress_faults_directive_one_line : nosuppress_faults_directive Spaces* CR  ;
nosuppress_faults_directive : TICK_NOSUPPRESS_FAULTS;

suppress_faults_directive_one_line : suppress_faults_directive Spaces* CR  ;
suppress_faults_directive : TICK_SUPPRESS_FAULTS;

signed_directive_one_line : signed_directive Spaces* CR ;
signed_directive : TICK_SIGNED;

unsigned_directive_one_line : unsigned_directive Spaces* CR ;
unsigned_directive : TICK_UNSIGNED;

remove_gatename_directive_one_line : remove_gatename_directive Spaces* CR ;
remove_gatename_directive : TICK_REMOVE_GATENAME;

noremove_gatenames_directive_one_line : noremove_gatenames_directive Spaces* CR ;
noremove_gatenames_directive : TICK_NOREMOVE_GATENAMES;

remove_netname_directive_one_line : remove_netname_directive Spaces* CR ;
remove_netname_directive : TICK_REMOVE_NETNAME;

noremove_netnames_directive_one_line : noremove_netnames_directive Spaces* CR ; 
noremove_netnames_directive : TICK_NOREMOVE_NETNAMES; 

accelerate_directive_one_line : accelerate_directive Spaces* CR ;
accelerate_directive : TICK_ACCELERATE;

noaccelerate_directive_one_line : noaccelerate_directive Spaces* CR ;
noaccelerate_directive : TICK_NOACCELERATE;

default_trireg_strenght_directive_one_line : default_trireg_strenght_directive Spaces* CR ;
default_trireg_strenght_directive : TICK_DEFAULT_TRIREG_STRENGTH Spaces number;

default_decay_time_directive_one_line : default_decay_time_directive Spaces* CR ;
default_decay_time_directive : TICK_DEFAULT_DECAY_TIME Spaces ( number | Simple_identifier | Fixed_point_number );

unconnected_drive_directive_one_line : unconnected_drive_directive Spaces* CR ;
unconnected_drive_directive : TICK_UNCONNECTED_DRIVE Spaces Simple_identifier;

nounconnected_drive_directive_one_line : nounconnected_drive_directive Spaces* CR ;
nounconnected_drive_directive : TICK_NOUNCONNECTED_DRIVE;

delay_mode_distributed_directive_one_line : delay_mode_distributed_directive Spaces* CR ;    
delay_mode_distributed_directive : TICK_DELAY_MODE_DISTRIBUTED;    

delay_mode_path_directive_one_line : delay_mode_path_directive Spaces* CR ;   
delay_mode_path_directive : TICK_DELAY_MODE_PATH;   

delay_mode_unit_directive_one_line : delay_mode_unit_directive Spaces* CR ;         
delay_mode_unit_directive : TICK_DELAY_MODE_UNIT;         

delay_mode_zero_directive_one_line : delay_mode_zero_directive Spaces* CR ;
delay_mode_zero_directive : TICK_DELAY_MODE_ZERO;

undefineall_directive : TICK_UNDEFINEALL; 

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

define_directive : TICK_DEFINE Spaces (Simple_identifier | Escaped_identifier) Spaces* CR ;

multiline_no_args_macro_definition : TICK_DEFINE Spaces (Simple_identifier | Escaped_identifier) Spaces* escaped_macro_definition_body  ;

multiline_args_macro_definition : TICK_DEFINE Spaces (Simple_identifier | Escaped_identifier) macro_arguments Spaces* escaped_macro_definition_body;

simple_no_args_macro_definition :
              TICK_DEFINE Spaces (Simple_identifier | Escaped_identifier) Spaces simple_macro_definition_body (CR | One_line_comment)
            | TICK_DEFINE Spaces (Simple_identifier | Escaped_identifier) Spaces* CR
	    ;

simple_args_macro_definition :
              TICK_DEFINE Spaces (Simple_identifier | Escaped_identifier) macro_arguments Spaces simple_macro_definition_body (CR | One_line_comment)
            | TICK_DEFINE Spaces (Simple_identifier | Escaped_identifier) macro_arguments Spaces* CR 
            ;

identifier_in_macro_body : (Simple_identifier TICK_TICK?)* ;

simple_no_args_macro_definition_in_macro_body :
              TICK_DEFINE Spaces (identifier_in_macro_body | Escaped_identifier)  Spaces simple_macro_definition_body_in_macro_body
            | TICK_DEFINE Spaces (identifier_in_macro_body | Escaped_identifier) Spaces*
	    | TICK_DEFINE Spaces (identifier_in_macro_body | Escaped_identifier) TICK_VARIABLE simple_macro_definition_body_in_macro_body
	    ;

simple_args_macro_definition_in_macro_body :
              TICK_DEFINE Spaces (identifier_in_macro_body | Escaped_identifier) macro_arguments Spaces simple_macro_definition_body_in_macro_body
            | TICK_DEFINE Spaces (identifier_in_macro_body | Escaped_identifier) macro_arguments
            ;

directive_in_macro : 
              celldefine_directive 
            | endcelldefine_directive
            | default_nettype_directive
            | undef_directive
            | ifdef_directive
            | ifndef_directive 
            | else_directive 
            | elsif_directive
            | elseif_directive
            | endif_directive 
            | include_directive
            | resetall_directive
            | timescale_directive
            | unconnected_drive_directive
            | nounconnected_drive_directive 
            | line_directive
            | default_decay_time_directive
            | default_trireg_strenght_directive
            | delay_mode_distributed_directive   
            | delay_mode_path_directive   
            | delay_mode_unit_directive         
            | delay_mode_zero_directive
	    | protect_directive 
	    | endprotect_directive 
	    | protected_directive 
	    | endprotected_directive 
	    | expand_vectornets_directive 
	    | noexpand_vectornets_directive 
	    | autoexpand_vectornets_directive
	    | remove_gatename_directive 
	    | noremove_gatenames_directive 
	    | remove_netname_directive 
 	    | noremove_netnames_directive
	    | accelerate_directive
	    | noaccelerate_directive
            | undefineall_directive
	    | uselib_directive
	    | disable_portfaults_directive
	    | enable_portfaults_directive 
	    | nosuppress_faults_directive 
	    | suppress_faults_directive 
	    | signed_directive 
	    | unsigned_directive
	    | sv_file_directive 
            | sv_line_directive
	    | sv_package
	    | endpackage
	    | simple_args_macro_definition_in_macro_body //(ESCAPED_CR | CR) Adds long runtime on Verilator t_preproc.v case but fixes Syntax Error 
	    | simple_no_args_macro_definition_in_macro_body //(ESCAPED_CR | CR)
	    | pound_delay
	    ;

macro_arguments : PARENS_OPEN ((Simple_identifier Spaces* (EQUAL_OP default_value*)*)
                               (COMMA Spaces* (Simple_identifier Spaces* (EQUAL_OP default_value*)*))*)* PARENS_CLOSE ;

escaped_macro_definition_body : escaped_macro_definition_body_alt1
                              | escaped_macro_definition_body_alt2;

escaped_macro_definition_body_alt1 : (  unterminated_string | Macro_identifier | Macro_Escaped_identifier |
                                        escaped_identifier | Simple_identifier |
                                        number | TEXT_CR | pound_delay | ESCAPED_CR | PARENS_OPEN | PARENS_CLOSE | COMMA |
					EQUAL_OP | DOUBLE_QUOTE | TICK_VARIABLE | directive_in_macro | Spaces |
					Fixed_point_number | String | comments | TICK_QUOTE | TICK_BACKSLASH_TICK_QUOTE |
					TICK_TICK | Special | CURLY_OPEN | CURLY_CLOSE | SQUARE_OPEN |
					SQUARE_CLOSE)*? ESCAPED_CR Spaces* (CR | EOF);

escaped_macro_definition_body_alt2 : (  unterminated_string | Macro_identifier | Macro_Escaped_identifier |
                                        escaped_identifier |
                                        Simple_identifier | number | TEXT_CR | pound_delay | ESCAPED_CR | PARENS_OPEN |
					PARENS_CLOSE | COMMA | EQUAL_OP | DOUBLE_QUOTE | TICK_VARIABLE |
			                directive_in_macro | Spaces | Fixed_point_number | String | comments |
					TICK_QUOTE | TICK_BACKSLASH_TICK_QUOTE | TICK_TICK | Special | CURLY_OPEN |
					CURLY_CLOSE | SQUARE_OPEN | SQUARE_CLOSE)*? (CR Spaces* | EOF) ;

simple_macro_definition_body : (  unterminated_string | Macro_identifier | Macro_Escaped_identifier |
                                  escaped_identifier |
                                  Simple_identifier | number | pound_delay | TEXT_CR | PARENS_OPEN |
				  PARENS_CLOSE | COMMA | EQUAL_OP | DOUBLE_QUOTE | TICK_VARIABLE |
				  Spaces | Fixed_point_number | String | comments |
				  TICK_QUOTE | TICK_BACKSLASH_TICK_QUOTE | TICK_TICK | Special |
				  CURLY_OPEN | CURLY_CLOSE | SQUARE_OPEN | SQUARE_CLOSE | TICK_INCLUDE | directive_in_macro )*? ;

simple_macro_definition_body_in_macro_body : (  unterminated_string | Macro_identifier | Macro_Escaped_identifier |
                                  escaped_identifier |
                                  Simple_identifier | number | pound_delay | TEXT_CR | 
                                  PARENS_OPEN | PARENS_CLOSE | COMMA | EQUAL_OP | DOUBLE_QUOTE | TICK_VARIABLE |
				  Spaces | Fixed_point_number | String | comments |
				  TICK_QUOTE | TICK_BACKSLASH_TICK_QUOTE | TICK_TICK | Special | CURLY_OPEN |
				  CURLY_CLOSE | SQUARE_OPEN | SQUARE_CLOSE )*? ;


pragma_expression : Simple_identifier
	         | number
		 | Spaces
	         | Fixed_point_number
	         | String
	         | Special
		 | CURLY_OPEN
		 | CURLY_CLOSE
		 | SQUARE_OPEN
		 | SQUARE_CLOSE
	         | PARENS_OPEN
	         | PARENS_CLOSE
	         | COMMA
	         | EQUAL_OP
	         | DOUBLE_QUOTE 
	         | ANY
		 | escaped_identifier
		 | pound_delay 
	         ;

macro_arg : Simple_identifier
	         | number
	         | Spaces
	         | Fixed_point_number
	         | String
	         | Special
		 | paired_parens
	         | COMMA
	         | EQUAL_OP
	         | DOUBLE_QUOTE 
		 | macro_instance
		 | CR
		 | TEXT_CR
	         | ANY
		 | escaped_identifier
                 | simple_args_macro_definition_in_macro_body
	         | simple_no_args_macro_definition_in_macro_body
	         ;

paired_parens : ( PARENS_OPEN ( Simple_identifier | number
	         | Spaces | Fixed_point_number | String | Special | COMMA | EQUAL_OP
	         | DOUBLE_QUOTE | macro_instance | TEXT_CR | CR | ANY | paired_parens | escaped_identifier )* PARENS_CLOSE )
              | ( CURLY_OPEN ( Simple_identifier | number
	         | Spaces | Fixed_point_number | String | Special | COMMA | EQUAL_OP
	         | DOUBLE_QUOTE | macro_instance | CR | ANY | paired_parens | escaped_identifier )* CURLY_CLOSE )
	      | ( SQUARE_OPEN ( Simple_identifier | number
	         | Spaces | Fixed_point_number | String | Special | COMMA | EQUAL_OP
	         | DOUBLE_QUOTE | macro_instance | CR | ANY | paired_parens | escaped_identifier )* SQUARE_CLOSE ) ;

text_blob :   Simple_identifier
	    | number
	    | CR
	    | Spaces
	    | Fixed_point_number
	    | ESCAPED_CR
	    | String
	    | PARENS_OPEN
	    | PARENS_CLOSE
	    | COMMA
	    | EQUAL_OP
	    | DOUBLE_QUOTE 
	    | Special
	    | CURLY_OPEN
	    | CURLY_CLOSE
	    | SQUARE_OPEN
	    | SQUARE_CLOSE
	    | TICK_TICK
	    | TICK_VARIABLE
	    | TIMESCALE
	    | ANY
	    | pound_delay
	    | TICK_QUOTE
	    | TICK_BACKSLASH_TICK_QUOTE
	    | TEXT_CR
	    ;

string : String ;

escaped_identifier : Escaped_identifier;

default_value : Simple_identifier
	    | number
	    | Spaces
	    | Fixed_point_number
	    | String
	    | Special
	    | CURLY_OPEN
	    | CURLY_CLOSE
	    | SQUARE_OPEN
	    | SQUARE_CLOSE
	    | ANY
	    | escaped_identifier
	    ;

string_blob : Simple_identifier
	    | number
	    | Spaces
	    | Fixed_point_number
	    | ESCAPED_CR
	    | PARENS_OPEN
	    | PARENS_CLOSE
	    | COMMA
	    | EQUAL_OP
	    | DOUBLE_QUOTE 
	    | Special
	    | CURLY_OPEN
	    | CURLY_CLOSE
	    | SQUARE_OPEN
	    | SQUARE_CLOSE
	    | ANY
	    | escaped_identifier
	    | TIMESCALE
	    | pound_delay
	    | TEXT_CR
	    ;
