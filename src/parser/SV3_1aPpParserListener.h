
// Generated from SV3_1aPpParser.g4 by ANTLR 4.9.1

#pragma once


#include "antlr4-runtime.h"
#include "SV3_1aPpParser.h"


/**
 * This interface defines an abstract listener for a parse tree produced by SV3_1aPpParser.
 */
class  SV3_1aPpParserListener : public antlr4::tree::ParseTreeListener {
public:

  virtual void enterTop_level_rule(SV3_1aPpParser::Top_level_ruleContext *ctx) = 0;
  virtual void exitTop_level_rule(SV3_1aPpParser::Top_level_ruleContext *ctx) = 0;

  virtual void enterSource_text(SV3_1aPpParser::Source_textContext *ctx) = 0;
  virtual void exitSource_text(SV3_1aPpParser::Source_textContext *ctx) = 0;

  virtual void enterNull_rule(SV3_1aPpParser::Null_ruleContext *ctx) = 0;
  virtual void exitNull_rule(SV3_1aPpParser::Null_ruleContext *ctx) = 0;

  virtual void enterDescription(SV3_1aPpParser::DescriptionContext *ctx) = 0;
  virtual void exitDescription(SV3_1aPpParser::DescriptionContext *ctx) = 0;

  virtual void enterMacroInstanceWithArgs(SV3_1aPpParser::MacroInstanceWithArgsContext *ctx) = 0;
  virtual void exitMacroInstanceWithArgs(SV3_1aPpParser::MacroInstanceWithArgsContext *ctx) = 0;

  virtual void enterMacroInstanceNoArgs(SV3_1aPpParser::MacroInstanceNoArgsContext *ctx) = 0;
  virtual void exitMacroInstanceNoArgs(SV3_1aPpParser::MacroInstanceNoArgsContext *ctx) = 0;

  virtual void enterUnterminated_string(SV3_1aPpParser::Unterminated_stringContext *ctx) = 0;
  virtual void exitUnterminated_string(SV3_1aPpParser::Unterminated_stringContext *ctx) = 0;

  virtual void enterMacro_actual_args(SV3_1aPpParser::Macro_actual_argsContext *ctx) = 0;
  virtual void exitMacro_actual_args(SV3_1aPpParser::Macro_actual_argsContext *ctx) = 0;

  virtual void enterComments(SV3_1aPpParser::CommentsContext *ctx) = 0;
  virtual void exitComments(SV3_1aPpParser::CommentsContext *ctx) = 0;

  virtual void enterNumber(SV3_1aPpParser::NumberContext *ctx) = 0;
  virtual void exitNumber(SV3_1aPpParser::NumberContext *ctx) = 0;

  virtual void enterPound_delay(SV3_1aPpParser::Pound_delayContext *ctx) = 0;
  virtual void exitPound_delay(SV3_1aPpParser::Pound_delayContext *ctx) = 0;

  virtual void enterPound_pound_delay(SV3_1aPpParser::Pound_pound_delayContext *ctx) = 0;
  virtual void exitPound_pound_delay(SV3_1aPpParser::Pound_pound_delayContext *ctx) = 0;

  virtual void enterMacro_definition(SV3_1aPpParser::Macro_definitionContext *ctx) = 0;
  virtual void exitMacro_definition(SV3_1aPpParser::Macro_definitionContext *ctx) = 0;

  virtual void enterInclude_directive(SV3_1aPpParser::Include_directiveContext *ctx) = 0;
  virtual void exitInclude_directive(SV3_1aPpParser::Include_directiveContext *ctx) = 0;

  virtual void enterLine_directive(SV3_1aPpParser::Line_directiveContext *ctx) = 0;
  virtual void exitLine_directive(SV3_1aPpParser::Line_directiveContext *ctx) = 0;

  virtual void enterDefault_nettype_directive(SV3_1aPpParser::Default_nettype_directiveContext *ctx) = 0;
  virtual void exitDefault_nettype_directive(SV3_1aPpParser::Default_nettype_directiveContext *ctx) = 0;

  virtual void enterSv_file_directive(SV3_1aPpParser::Sv_file_directiveContext *ctx) = 0;
  virtual void exitSv_file_directive(SV3_1aPpParser::Sv_file_directiveContext *ctx) = 0;

  virtual void enterSv_line_directive(SV3_1aPpParser::Sv_line_directiveContext *ctx) = 0;
  virtual void exitSv_line_directive(SV3_1aPpParser::Sv_line_directiveContext *ctx) = 0;

  virtual void enterTimescale_directive(SV3_1aPpParser::Timescale_directiveContext *ctx) = 0;
  virtual void exitTimescale_directive(SV3_1aPpParser::Timescale_directiveContext *ctx) = 0;

  virtual void enterUndef_directive(SV3_1aPpParser::Undef_directiveContext *ctx) = 0;
  virtual void exitUndef_directive(SV3_1aPpParser::Undef_directiveContext *ctx) = 0;

  virtual void enterIfdef_directive(SV3_1aPpParser::Ifdef_directiveContext *ctx) = 0;
  virtual void exitIfdef_directive(SV3_1aPpParser::Ifdef_directiveContext *ctx) = 0;

  virtual void enterIfdef_directive_in_macro_body(SV3_1aPpParser::Ifdef_directive_in_macro_bodyContext *ctx) = 0;
  virtual void exitIfdef_directive_in_macro_body(SV3_1aPpParser::Ifdef_directive_in_macro_bodyContext *ctx) = 0;

  virtual void enterIfndef_directive(SV3_1aPpParser::Ifndef_directiveContext *ctx) = 0;
  virtual void exitIfndef_directive(SV3_1aPpParser::Ifndef_directiveContext *ctx) = 0;

  virtual void enterIfndef_directive_in_macro_body(SV3_1aPpParser::Ifndef_directive_in_macro_bodyContext *ctx) = 0;
  virtual void exitIfndef_directive_in_macro_body(SV3_1aPpParser::Ifndef_directive_in_macro_bodyContext *ctx) = 0;

  virtual void enterElsif_directive(SV3_1aPpParser::Elsif_directiveContext *ctx) = 0;
  virtual void exitElsif_directive(SV3_1aPpParser::Elsif_directiveContext *ctx) = 0;

  virtual void enterElsif_directive_in_macro_body(SV3_1aPpParser::Elsif_directive_in_macro_bodyContext *ctx) = 0;
  virtual void exitElsif_directive_in_macro_body(SV3_1aPpParser::Elsif_directive_in_macro_bodyContext *ctx) = 0;

  virtual void enterElseif_directive(SV3_1aPpParser::Elseif_directiveContext *ctx) = 0;
  virtual void exitElseif_directive(SV3_1aPpParser::Elseif_directiveContext *ctx) = 0;

  virtual void enterElseif_directive_in_macro_body(SV3_1aPpParser::Elseif_directive_in_macro_bodyContext *ctx) = 0;
  virtual void exitElseif_directive_in_macro_body(SV3_1aPpParser::Elseif_directive_in_macro_bodyContext *ctx) = 0;

  virtual void enterElse_directive(SV3_1aPpParser::Else_directiveContext *ctx) = 0;
  virtual void exitElse_directive(SV3_1aPpParser::Else_directiveContext *ctx) = 0;

  virtual void enterEndif_directive(SV3_1aPpParser::Endif_directiveContext *ctx) = 0;
  virtual void exitEndif_directive(SV3_1aPpParser::Endif_directiveContext *ctx) = 0;

  virtual void enterResetall_directive(SV3_1aPpParser::Resetall_directiveContext *ctx) = 0;
  virtual void exitResetall_directive(SV3_1aPpParser::Resetall_directiveContext *ctx) = 0;

  virtual void enterBegin_keywords_directive(SV3_1aPpParser::Begin_keywords_directiveContext *ctx) = 0;
  virtual void exitBegin_keywords_directive(SV3_1aPpParser::Begin_keywords_directiveContext *ctx) = 0;

  virtual void enterEnd_keywords_directive(SV3_1aPpParser::End_keywords_directiveContext *ctx) = 0;
  virtual void exitEnd_keywords_directive(SV3_1aPpParser::End_keywords_directiveContext *ctx) = 0;

  virtual void enterPragma_directive(SV3_1aPpParser::Pragma_directiveContext *ctx) = 0;
  virtual void exitPragma_directive(SV3_1aPpParser::Pragma_directiveContext *ctx) = 0;

  virtual void enterCelldefine_directive(SV3_1aPpParser::Celldefine_directiveContext *ctx) = 0;
  virtual void exitCelldefine_directive(SV3_1aPpParser::Celldefine_directiveContext *ctx) = 0;

  virtual void enterEndcelldefine_directive(SV3_1aPpParser::Endcelldefine_directiveContext *ctx) = 0;
  virtual void exitEndcelldefine_directive(SV3_1aPpParser::Endcelldefine_directiveContext *ctx) = 0;

  virtual void enterProtect_directive(SV3_1aPpParser::Protect_directiveContext *ctx) = 0;
  virtual void exitProtect_directive(SV3_1aPpParser::Protect_directiveContext *ctx) = 0;

  virtual void enterEndprotect_directive(SV3_1aPpParser::Endprotect_directiveContext *ctx) = 0;
  virtual void exitEndprotect_directive(SV3_1aPpParser::Endprotect_directiveContext *ctx) = 0;

  virtual void enterProtected_directive(SV3_1aPpParser::Protected_directiveContext *ctx) = 0;
  virtual void exitProtected_directive(SV3_1aPpParser::Protected_directiveContext *ctx) = 0;

  virtual void enterEndprotected_directive(SV3_1aPpParser::Endprotected_directiveContext *ctx) = 0;
  virtual void exitEndprotected_directive(SV3_1aPpParser::Endprotected_directiveContext *ctx) = 0;

  virtual void enterExpand_vectornets_directive(SV3_1aPpParser::Expand_vectornets_directiveContext *ctx) = 0;
  virtual void exitExpand_vectornets_directive(SV3_1aPpParser::Expand_vectornets_directiveContext *ctx) = 0;

  virtual void enterNoexpand_vectornets_directive(SV3_1aPpParser::Noexpand_vectornets_directiveContext *ctx) = 0;
  virtual void exitNoexpand_vectornets_directive(SV3_1aPpParser::Noexpand_vectornets_directiveContext *ctx) = 0;

  virtual void enterAutoexpand_vectornets_directive(SV3_1aPpParser::Autoexpand_vectornets_directiveContext *ctx) = 0;
  virtual void exitAutoexpand_vectornets_directive(SV3_1aPpParser::Autoexpand_vectornets_directiveContext *ctx) = 0;

  virtual void enterUselib_directive(SV3_1aPpParser::Uselib_directiveContext *ctx) = 0;
  virtual void exitUselib_directive(SV3_1aPpParser::Uselib_directiveContext *ctx) = 0;

  virtual void enterDisable_portfaults_directive(SV3_1aPpParser::Disable_portfaults_directiveContext *ctx) = 0;
  virtual void exitDisable_portfaults_directive(SV3_1aPpParser::Disable_portfaults_directiveContext *ctx) = 0;

  virtual void enterEnable_portfaults_directive(SV3_1aPpParser::Enable_portfaults_directiveContext *ctx) = 0;
  virtual void exitEnable_portfaults_directive(SV3_1aPpParser::Enable_portfaults_directiveContext *ctx) = 0;

  virtual void enterNosuppress_faults_directive(SV3_1aPpParser::Nosuppress_faults_directiveContext *ctx) = 0;
  virtual void exitNosuppress_faults_directive(SV3_1aPpParser::Nosuppress_faults_directiveContext *ctx) = 0;

  virtual void enterSuppress_faults_directive(SV3_1aPpParser::Suppress_faults_directiveContext *ctx) = 0;
  virtual void exitSuppress_faults_directive(SV3_1aPpParser::Suppress_faults_directiveContext *ctx) = 0;

  virtual void enterSigned_directive(SV3_1aPpParser::Signed_directiveContext *ctx) = 0;
  virtual void exitSigned_directive(SV3_1aPpParser::Signed_directiveContext *ctx) = 0;

  virtual void enterUnsigned_directive(SV3_1aPpParser::Unsigned_directiveContext *ctx) = 0;
  virtual void exitUnsigned_directive(SV3_1aPpParser::Unsigned_directiveContext *ctx) = 0;

  virtual void enterRemove_gatename_directive(SV3_1aPpParser::Remove_gatename_directiveContext *ctx) = 0;
  virtual void exitRemove_gatename_directive(SV3_1aPpParser::Remove_gatename_directiveContext *ctx) = 0;

  virtual void enterNoremove_gatenames_directive(SV3_1aPpParser::Noremove_gatenames_directiveContext *ctx) = 0;
  virtual void exitNoremove_gatenames_directive(SV3_1aPpParser::Noremove_gatenames_directiveContext *ctx) = 0;

  virtual void enterRemove_netname_directive(SV3_1aPpParser::Remove_netname_directiveContext *ctx) = 0;
  virtual void exitRemove_netname_directive(SV3_1aPpParser::Remove_netname_directiveContext *ctx) = 0;

  virtual void enterNoremove_netnames_directive(SV3_1aPpParser::Noremove_netnames_directiveContext *ctx) = 0;
  virtual void exitNoremove_netnames_directive(SV3_1aPpParser::Noremove_netnames_directiveContext *ctx) = 0;

  virtual void enterAccelerate_directive(SV3_1aPpParser::Accelerate_directiveContext *ctx) = 0;
  virtual void exitAccelerate_directive(SV3_1aPpParser::Accelerate_directiveContext *ctx) = 0;

  virtual void enterNoaccelerate_directive(SV3_1aPpParser::Noaccelerate_directiveContext *ctx) = 0;
  virtual void exitNoaccelerate_directive(SV3_1aPpParser::Noaccelerate_directiveContext *ctx) = 0;

  virtual void enterDefault_trireg_strenght_directive(SV3_1aPpParser::Default_trireg_strenght_directiveContext *ctx) = 0;
  virtual void exitDefault_trireg_strenght_directive(SV3_1aPpParser::Default_trireg_strenght_directiveContext *ctx) = 0;

  virtual void enterDefault_decay_time_directive(SV3_1aPpParser::Default_decay_time_directiveContext *ctx) = 0;
  virtual void exitDefault_decay_time_directive(SV3_1aPpParser::Default_decay_time_directiveContext *ctx) = 0;

  virtual void enterUnconnected_drive_directive(SV3_1aPpParser::Unconnected_drive_directiveContext *ctx) = 0;
  virtual void exitUnconnected_drive_directive(SV3_1aPpParser::Unconnected_drive_directiveContext *ctx) = 0;

  virtual void enterNounconnected_drive_directive(SV3_1aPpParser::Nounconnected_drive_directiveContext *ctx) = 0;
  virtual void exitNounconnected_drive_directive(SV3_1aPpParser::Nounconnected_drive_directiveContext *ctx) = 0;

  virtual void enterDelay_mode_distributed_directive(SV3_1aPpParser::Delay_mode_distributed_directiveContext *ctx) = 0;
  virtual void exitDelay_mode_distributed_directive(SV3_1aPpParser::Delay_mode_distributed_directiveContext *ctx) = 0;

  virtual void enterDelay_mode_path_directive(SV3_1aPpParser::Delay_mode_path_directiveContext *ctx) = 0;
  virtual void exitDelay_mode_path_directive(SV3_1aPpParser::Delay_mode_path_directiveContext *ctx) = 0;

  virtual void enterDelay_mode_unit_directive(SV3_1aPpParser::Delay_mode_unit_directiveContext *ctx) = 0;
  virtual void exitDelay_mode_unit_directive(SV3_1aPpParser::Delay_mode_unit_directiveContext *ctx) = 0;

  virtual void enterDelay_mode_zero_directive(SV3_1aPpParser::Delay_mode_zero_directiveContext *ctx) = 0;
  virtual void exitDelay_mode_zero_directive(SV3_1aPpParser::Delay_mode_zero_directiveContext *ctx) = 0;

  virtual void enterUndefineall_directive(SV3_1aPpParser::Undefineall_directiveContext *ctx) = 0;
  virtual void exitUndefineall_directive(SV3_1aPpParser::Undefineall_directiveContext *ctx) = 0;

  virtual void enterModule(SV3_1aPpParser::ModuleContext *ctx) = 0;
  virtual void exitModule(SV3_1aPpParser::ModuleContext *ctx) = 0;

  virtual void enterEndmodule(SV3_1aPpParser::EndmoduleContext *ctx) = 0;
  virtual void exitEndmodule(SV3_1aPpParser::EndmoduleContext *ctx) = 0;

  virtual void enterSv_interface(SV3_1aPpParser::Sv_interfaceContext *ctx) = 0;
  virtual void exitSv_interface(SV3_1aPpParser::Sv_interfaceContext *ctx) = 0;

  virtual void enterEndinterface(SV3_1aPpParser::EndinterfaceContext *ctx) = 0;
  virtual void exitEndinterface(SV3_1aPpParser::EndinterfaceContext *ctx) = 0;

  virtual void enterProgram(SV3_1aPpParser::ProgramContext *ctx) = 0;
  virtual void exitProgram(SV3_1aPpParser::ProgramContext *ctx) = 0;

  virtual void enterEndprogram(SV3_1aPpParser::EndprogramContext *ctx) = 0;
  virtual void exitEndprogram(SV3_1aPpParser::EndprogramContext *ctx) = 0;

  virtual void enterPrimitive(SV3_1aPpParser::PrimitiveContext *ctx) = 0;
  virtual void exitPrimitive(SV3_1aPpParser::PrimitiveContext *ctx) = 0;

  virtual void enterEndprimitive(SV3_1aPpParser::EndprimitiveContext *ctx) = 0;
  virtual void exitEndprimitive(SV3_1aPpParser::EndprimitiveContext *ctx) = 0;

  virtual void enterSv_package(SV3_1aPpParser::Sv_packageContext *ctx) = 0;
  virtual void exitSv_package(SV3_1aPpParser::Sv_packageContext *ctx) = 0;

  virtual void enterEndpackage(SV3_1aPpParser::EndpackageContext *ctx) = 0;
  virtual void exitEndpackage(SV3_1aPpParser::EndpackageContext *ctx) = 0;

  virtual void enterChecker(SV3_1aPpParser::CheckerContext *ctx) = 0;
  virtual void exitChecker(SV3_1aPpParser::CheckerContext *ctx) = 0;

  virtual void enterEndchecker(SV3_1aPpParser::EndcheckerContext *ctx) = 0;
  virtual void exitEndchecker(SV3_1aPpParser::EndcheckerContext *ctx) = 0;

  virtual void enterConfig(SV3_1aPpParser::ConfigContext *ctx) = 0;
  virtual void exitConfig(SV3_1aPpParser::ConfigContext *ctx) = 0;

  virtual void enterEndconfig(SV3_1aPpParser::EndconfigContext *ctx) = 0;
  virtual void exitEndconfig(SV3_1aPpParser::EndconfigContext *ctx) = 0;

  virtual void enterDefine_directive(SV3_1aPpParser::Define_directiveContext *ctx) = 0;
  virtual void exitDefine_directive(SV3_1aPpParser::Define_directiveContext *ctx) = 0;

  virtual void enterMultiline_no_args_macro_definition(SV3_1aPpParser::Multiline_no_args_macro_definitionContext *ctx) = 0;
  virtual void exitMultiline_no_args_macro_definition(SV3_1aPpParser::Multiline_no_args_macro_definitionContext *ctx) = 0;

  virtual void enterMultiline_args_macro_definition(SV3_1aPpParser::Multiline_args_macro_definitionContext *ctx) = 0;
  virtual void exitMultiline_args_macro_definition(SV3_1aPpParser::Multiline_args_macro_definitionContext *ctx) = 0;

  virtual void enterSimple_no_args_macro_definition(SV3_1aPpParser::Simple_no_args_macro_definitionContext *ctx) = 0;
  virtual void exitSimple_no_args_macro_definition(SV3_1aPpParser::Simple_no_args_macro_definitionContext *ctx) = 0;

  virtual void enterSimple_args_macro_definition(SV3_1aPpParser::Simple_args_macro_definitionContext *ctx) = 0;
  virtual void exitSimple_args_macro_definition(SV3_1aPpParser::Simple_args_macro_definitionContext *ctx) = 0;

  virtual void enterIdentifier_in_macro_body(SV3_1aPpParser::Identifier_in_macro_bodyContext *ctx) = 0;
  virtual void exitIdentifier_in_macro_body(SV3_1aPpParser::Identifier_in_macro_bodyContext *ctx) = 0;

  virtual void enterSimple_no_args_macro_definition_in_macro_body(SV3_1aPpParser::Simple_no_args_macro_definition_in_macro_bodyContext *ctx) = 0;
  virtual void exitSimple_no_args_macro_definition_in_macro_body(SV3_1aPpParser::Simple_no_args_macro_definition_in_macro_bodyContext *ctx) = 0;

  virtual void enterSimple_args_macro_definition_in_macro_body(SV3_1aPpParser::Simple_args_macro_definition_in_macro_bodyContext *ctx) = 0;
  virtual void exitSimple_args_macro_definition_in_macro_body(SV3_1aPpParser::Simple_args_macro_definition_in_macro_bodyContext *ctx) = 0;

  virtual void enterDirective_in_macro(SV3_1aPpParser::Directive_in_macroContext *ctx) = 0;
  virtual void exitDirective_in_macro(SV3_1aPpParser::Directive_in_macroContext *ctx) = 0;

  virtual void enterMacro_arguments(SV3_1aPpParser::Macro_argumentsContext *ctx) = 0;
  virtual void exitMacro_arguments(SV3_1aPpParser::Macro_argumentsContext *ctx) = 0;

  virtual void enterEscaped_macro_definition_body(SV3_1aPpParser::Escaped_macro_definition_bodyContext *ctx) = 0;
  virtual void exitEscaped_macro_definition_body(SV3_1aPpParser::Escaped_macro_definition_bodyContext *ctx) = 0;

  virtual void enterEscaped_macro_definition_body_alt1(SV3_1aPpParser::Escaped_macro_definition_body_alt1Context *ctx) = 0;
  virtual void exitEscaped_macro_definition_body_alt1(SV3_1aPpParser::Escaped_macro_definition_body_alt1Context *ctx) = 0;

  virtual void enterEscaped_macro_definition_body_alt2(SV3_1aPpParser::Escaped_macro_definition_body_alt2Context *ctx) = 0;
  virtual void exitEscaped_macro_definition_body_alt2(SV3_1aPpParser::Escaped_macro_definition_body_alt2Context *ctx) = 0;

  virtual void enterSimple_macro_definition_body(SV3_1aPpParser::Simple_macro_definition_bodyContext *ctx) = 0;
  virtual void exitSimple_macro_definition_body(SV3_1aPpParser::Simple_macro_definition_bodyContext *ctx) = 0;

  virtual void enterSimple_macro_definition_body_in_macro_body(SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext *ctx) = 0;
  virtual void exitSimple_macro_definition_body_in_macro_body(SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext *ctx) = 0;

  virtual void enterPragma_expression(SV3_1aPpParser::Pragma_expressionContext *ctx) = 0;
  virtual void exitPragma_expression(SV3_1aPpParser::Pragma_expressionContext *ctx) = 0;

  virtual void enterMacro_arg(SV3_1aPpParser::Macro_argContext *ctx) = 0;
  virtual void exitMacro_arg(SV3_1aPpParser::Macro_argContext *ctx) = 0;

  virtual void enterPaired_parens(SV3_1aPpParser::Paired_parensContext *ctx) = 0;
  virtual void exitPaired_parens(SV3_1aPpParser::Paired_parensContext *ctx) = 0;

  virtual void enterText_blob(SV3_1aPpParser::Text_blobContext *ctx) = 0;
  virtual void exitText_blob(SV3_1aPpParser::Text_blobContext *ctx) = 0;

  virtual void enterString(SV3_1aPpParser::StringContext *ctx) = 0;
  virtual void exitString(SV3_1aPpParser::StringContext *ctx) = 0;

  virtual void enterEscaped_identifier(SV3_1aPpParser::Escaped_identifierContext *ctx) = 0;
  virtual void exitEscaped_identifier(SV3_1aPpParser::Escaped_identifierContext *ctx) = 0;

  virtual void enterDefault_value(SV3_1aPpParser::Default_valueContext *ctx) = 0;
  virtual void exitDefault_value(SV3_1aPpParser::Default_valueContext *ctx) = 0;

  virtual void enterString_blob(SV3_1aPpParser::String_blobContext *ctx) = 0;
  virtual void exitString_blob(SV3_1aPpParser::String_blobContext *ctx) = 0;


};

