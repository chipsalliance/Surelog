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

parser grammar SV3_1aPpParser;

options { tokenVocab = SV3_1aPpLexer; }

top_level_rule : null_rule source_text EOF ; // SV files

source_text : ( description ) *;

null_rule : ; // Placeholder rule that create the "0" VObject, DO NOT REMOVE

description :
            unterminated_string
	    | string
	    | number
            | macro_definition
	    | comments 
            | celldefine_directive 
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
	    | begin_keywords_directive
	    | end_keywords_directive
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
	    | pragma_directive
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
	    | pound_pound_delay
	    ;

macro_instance : (Macro_identifier | Macro_Escaped_identifier) Spaces* PARENS_OPEN macro_actual_args PARENS_CLOSE # MacroInstanceWithArgs
	       | (Macro_identifier | Macro_Escaped_identifier)                                                    # MacroInstanceNoArgs
	       ;

unterminated_string : DOUBLE_QUOTE (string_blob)* CR;

macro_actual_args : (macro_arg)* (COMMA macro_arg*)* ;

comments :    One_line_comment 
	    | Block_comment 
	    ;

number : Number ;

pound_delay : Pound_delay ;

pound_pound_delay : Pound_Pound_delay ;

macro_definition :
              define_directive
	    | multiline_args_macro_definition
	    | simple_no_args_macro_definition	    
            | multiline_no_args_macro_definition
	    | simple_args_macro_definition	
	    ;

include_directive : TICK_INCLUDE Spaces (String | Simple_identifier | Escaped_identifier | macro_instance);

line_directive : TICK_LINE Spaces number String Spaces number;

default_nettype_directive : TICK_DEFAULT_NETTYPE Spaces Simple_identifier;

sv_file_directive : TICK_FILE__ ;

sv_line_directive : TICK_LINE__ ;

timescale_directive : TICK_TIMESCALE TIMESCALE ;

undef_directive : TICK_UNDEF Spaces (Simple_identifier | Escaped_identifier | macro_instance);

ifdef_directive : TICK_IFDEF Spaces (Simple_identifier | Escaped_identifier | macro_instance) ;
ifdef_directive_in_macro_body : TICK_IFDEF Spaces (identifier_in_macro_body | Escaped_identifier | macro_instance) ;

ifndef_directive : TICK_IFNDEF Spaces (Simple_identifier | Escaped_identifier | macro_instance);
ifndef_directive_in_macro_body : TICK_IFNDEF Spaces (identifier_in_macro_body | Escaped_identifier | macro_instance);

elsif_directive : TICK_ELSIF Spaces (Simple_identifier | Escaped_identifier | macro_instance);
elsif_directive_in_macro_body : TICK_ELSIF Spaces (identifier_in_macro_body | Escaped_identifier | macro_instance);

elseif_directive : TICK_ELSEIF Spaces (Simple_identifier | Escaped_identifier | macro_instance);
elseif_directive_in_macro_body : TICK_ELSEIF Spaces (identifier_in_macro_body | Escaped_identifier | macro_instance);

else_directive : TICK_ELSE;
			 
endif_directive : TICK_ENDIF Spaces* One_line_comment
		| TICK_ENDIF ;
  
resetall_directive : TICK_RESETALL;  
 
begin_keywords_directive : TICK_BEGIN_KEYWORDS Spaces String;
 
end_keywords_directive : TICK_END_KEYWORDS;

pragma_directive : TICK_PRAGMA Spaces Simple_identifier ( pragma_expression ( Special pragma_expression )* )* ;

celldefine_directive : TICK_CELLDEFINE Spaces* CR;

endcelldefine_directive : TICK_ENDCELLDEFINE Spaces* CR;

protect_directive : TICK_PROTECT Spaces* CR;
 
endprotect_directive : TICK_ENDPROTECT Spaces* CR; 

protected_directive : TICK_PROTECTED;

endprotected_directive : TICK_ENDPROTECTED; 

expand_vectornets_directive : TICK_EXPAND_VECTORNETS ;

noexpand_vectornets_directive : TICK_NOEXPAND_VECTORNETS;

autoexpand_vectornets_directive : TICK_AUTOEXPAND_VECTORNETS;

uselib_directive : TICK_USELIB ( text_blob )+;

disable_portfaults_directive : TICK_DISABLE_PORTFAULTS;

enable_portfaults_directive : TICK_ENABLE_PORTFAULTS;

nosuppress_faults_directive : TICK_NOSUPPRESS_FAULTS;

suppress_faults_directive : TICK_SUPPRESS_FAULTS;

signed_directive : TICK_SIGNED;

unsigned_directive : TICK_UNSIGNED;

remove_gatename_directive : TICK_REMOVE_GATENAME;

noremove_gatenames_directive : TICK_NOREMOVE_GATENAMES;

remove_netname_directive : TICK_REMOVE_NETNAME;

noremove_netnames_directive : TICK_NOREMOVE_NETNAMES; 

accelerate_directive : TICK_ACCELERATE;

noaccelerate_directive : TICK_NOACCELERATE;

default_trireg_strenght_directive : TICK_DEFAULT_TRIREG_STRENGTH Spaces number;

default_decay_time_directive : TICK_DEFAULT_DECAY_TIME Spaces ( number | Simple_identifier | Fixed_point_number );

unconnected_drive_directive : TICK_UNCONNECTED_DRIVE Spaces Simple_identifier;

nounconnected_drive_directive : TICK_NOUNCONNECTED_DRIVE Spaces* CR;

delay_mode_distributed_directive : TICK_DELAY_MODE_DISTRIBUTED;    

delay_mode_path_directive : TICK_DELAY_MODE_PATH;   
       
delay_mode_unit_directive : TICK_DELAY_MODE_UNIT;         

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
	    | module 
	    | endmodule
	    | sv_interface 
	    | endinterface 
	    | program 
	    | endprogram 
	    | primitive 
	    | endprimitive 
	    | checker
	    | endchecker 
	    | config 
	    | endconfig 
	    | simple_args_macro_definition_in_macro_body //(ESCAPED_CR | CR) Adds long runtime on Verilator t_preproc.v case but fixes Syntax Error 
	    | simple_no_args_macro_definition_in_macro_body //(ESCAPED_CR | CR)
	    | pound_delay
	    | pound_pound_delay
	    ;

macro_arguments : PARENS_OPEN ((Simple_identifier Spaces* (EQUAL_OP default_value*)*)
                               (COMMA Spaces* (Simple_identifier Spaces* (EQUAL_OP default_value*)*))*)* PARENS_CLOSE ;

escaped_macro_definition_body : escaped_macro_definition_body_alt1
                              | escaped_macro_definition_body_alt2;

escaped_macro_definition_body_alt1 : (  unterminated_string | Macro_identifier | Macro_Escaped_identifier |
                                        escaped_identifier | Simple_identifier |
                                        number | TEXT_CR | pound_delay | pound_pound_delay | ESCAPED_CR | PARENS_OPEN | PARENS_CLOSE | COMMA |
					EQUAL_OP | DOUBLE_QUOTE | TICK_VARIABLE | directive_in_macro | Spaces |
					Fixed_point_number | String | comments | TICK_QUOTE | TICK_BACKSLASH_TICK_QUOTE |
					TICK_TICK | Special | CURLY_OPEN | CURLY_CLOSE | SQUARE_OPEN |
					SQUARE_CLOSE)*? ESCAPED_CR Spaces* (CR | EOF);

escaped_macro_definition_body_alt2 : (  unterminated_string | Macro_identifier | Macro_Escaped_identifier |
                                        escaped_identifier |
                                        Simple_identifier | number | TEXT_CR | pound_delay | pound_pound_delay | ESCAPED_CR | PARENS_OPEN |
					PARENS_CLOSE | COMMA | EQUAL_OP | DOUBLE_QUOTE | TICK_VARIABLE |
			                directive_in_macro | Spaces | Fixed_point_number | String | comments |
					TICK_QUOTE | TICK_BACKSLASH_TICK_QUOTE | TICK_TICK | Special | CURLY_OPEN |
					CURLY_CLOSE | SQUARE_OPEN | SQUARE_CLOSE)*? (CR Spaces* | EOF) ;

simple_macro_definition_body : (  unterminated_string | Macro_identifier | Macro_Escaped_identifier |
                                  escaped_identifier |
                                  Simple_identifier | number | pound_delay | pound_pound_delay | TEXT_CR | PARENS_OPEN |
				  PARENS_CLOSE | COMMA | EQUAL_OP | DOUBLE_QUOTE | TICK_VARIABLE |
				  Spaces | Fixed_point_number | String | comments |
				  TICK_QUOTE | TICK_BACKSLASH_TICK_QUOTE | TICK_TICK | Special |
				  CURLY_OPEN | CURLY_CLOSE | SQUARE_OPEN | SQUARE_CLOSE | TICK_INCLUDE | directive_in_macro )*? ;

simple_macro_definition_body_in_macro_body : (  unterminated_string | Macro_identifier | Macro_Escaped_identifier |
                                  escaped_identifier |
                                  Simple_identifier | number | pound_delay | pound_pound_delay | TEXT_CR | 
                                  PARENS_OPEN | PARENS_CLOSE | COMMA | EQUAL_OP | DOUBLE_QUOTE | TICK_VARIABLE |
				  Spaces | Fixed_point_number | String | comments |
				  TICK_QUOTE | TICK_BACKSLASH_TICK_QUOTE | TICK_TICK | Special | CURLY_OPEN |
				  CURLY_CLOSE | SQUARE_OPEN | SQUARE_CLOSE )*? ;


pragma_expression : Simple_identifier
	         | number
		 | Spaces
	         | Fixed_point_number
	         | String
		 | CURLY_OPEN
		 | CURLY_CLOSE
		 | SQUARE_OPEN
		 | SQUARE_CLOSE
	         | PARENS_OPEN
	         | PARENS_CLOSE
	         | COMMA
	         | EQUAL_OP
	         | DOUBLE_QUOTE 
		 | escaped_identifier
		 | pound_delay 
		 | pound_pound_delay
	         | Special
	         | ANY
                 ;

macro_arg : Simple_identifier
	         | number
	         | Spaces
	         | Fixed_point_number
	         | String
		 | paired_parens
	         | EQUAL_OP
	         | DOUBLE_QUOTE 
		 | macro_instance
		 | CR
		 | TEXT_CR
		 | escaped_identifier
                 | simple_args_macro_definition_in_macro_body
	         | simple_no_args_macro_definition_in_macro_body
		 | comments
		 | pound_delay
	         | pound_pound_delay
	         | Special
	         | ANY
	         ;

paired_parens : ( PARENS_OPEN ( Simple_identifier | number
	         | Spaces | Fixed_point_number | String | COMMA | EQUAL_OP
	         | DOUBLE_QUOTE | macro_instance | TEXT_CR | CR | paired_parens | escaped_identifier | comments | Special | ANY )* PARENS_CLOSE )
              | ( CURLY_OPEN ( Simple_identifier | number
	         | Spaces | Fixed_point_number | String | COMMA | EQUAL_OP
	         | DOUBLE_QUOTE | macro_instance | CR | paired_parens | escaped_identifier | comments | Special | ANY )* CURLY_CLOSE )
	      | ( SQUARE_OPEN ( Simple_identifier | number
	         | Spaces | Fixed_point_number | String | COMMA | EQUAL_OP
	         | DOUBLE_QUOTE | macro_instance | CR | paired_parens | escaped_identifier | comments | Special | ANY )* SQUARE_CLOSE ) ;

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
	    | CURLY_OPEN
	    | CURLY_CLOSE
	    | SQUARE_OPEN
	    | SQUARE_CLOSE
	    | TICK_TICK
	    | TICK_VARIABLE
	    | TIMESCALE
	    | pound_delay
	    | pound_pound_delay
	    | TICK_QUOTE
	    | TICK_BACKSLASH_TICK_QUOTE
	    | TEXT_CR
	    | Special
	    | ANY
	    ;

string : String ;

escaped_identifier : Escaped_identifier;

default_value : Simple_identifier
	    | number
	    | Spaces
	    | Fixed_point_number
	    | String
	    | CURLY_OPEN
	    | CURLY_CLOSE
	    | SQUARE_OPEN
	    | SQUARE_CLOSE
	    | paired_parens
	    | escaped_identifier
	    | macro_instance
	    | Special
	    | ANY
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
	    | CURLY_OPEN
	    | CURLY_CLOSE
	    | SQUARE_OPEN
	    | SQUARE_CLOSE
	    | escaped_identifier
	    | TIMESCALE
	    | pound_delay
	    | pound_pound_delay
	    | TEXT_CR
	    | Special
	    | ANY
	    ;
