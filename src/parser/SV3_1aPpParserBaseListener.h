
// Generated from SV3_1aPpParser.g4 by ANTLR 4.9.1

#pragma once


#include "antlr4-runtime.h"
#include "SV3_1aPpParserListener.h"


/**
 * This class provides an empty implementation of SV3_1aPpParserListener,
 * which can be extended to create a listener which only needs to handle a subset
 * of the available methods.
 */
class  SV3_1aPpParserBaseListener : public SV3_1aPpParserListener {
public:

  virtual void enterTop_level_rule(SV3_1aPpParser::Top_level_ruleContext * /*ctx*/) override { }
  virtual void exitTop_level_rule(SV3_1aPpParser::Top_level_ruleContext * /*ctx*/) override { }

  virtual void enterSource_text(SV3_1aPpParser::Source_textContext * /*ctx*/) override { }
  virtual void exitSource_text(SV3_1aPpParser::Source_textContext * /*ctx*/) override { }

  virtual void enterNull_rule(SV3_1aPpParser::Null_ruleContext * /*ctx*/) override { }
  virtual void exitNull_rule(SV3_1aPpParser::Null_ruleContext * /*ctx*/) override { }

  virtual void enterDescription(SV3_1aPpParser::DescriptionContext * /*ctx*/) override { }
  virtual void exitDescription(SV3_1aPpParser::DescriptionContext * /*ctx*/) override { }

  virtual void enterMacroInstanceWithArgs(SV3_1aPpParser::MacroInstanceWithArgsContext * /*ctx*/) override { }
  virtual void exitMacroInstanceWithArgs(SV3_1aPpParser::MacroInstanceWithArgsContext * /*ctx*/) override { }

  virtual void enterMacroInstanceNoArgs(SV3_1aPpParser::MacroInstanceNoArgsContext * /*ctx*/) override { }
  virtual void exitMacroInstanceNoArgs(SV3_1aPpParser::MacroInstanceNoArgsContext * /*ctx*/) override { }

  virtual void enterUnterminated_string(SV3_1aPpParser::Unterminated_stringContext * /*ctx*/) override { }
  virtual void exitUnterminated_string(SV3_1aPpParser::Unterminated_stringContext * /*ctx*/) override { }

  virtual void enterMacro_actual_args(SV3_1aPpParser::Macro_actual_argsContext * /*ctx*/) override { }
  virtual void exitMacro_actual_args(SV3_1aPpParser::Macro_actual_argsContext * /*ctx*/) override { }

  virtual void enterComments(SV3_1aPpParser::CommentsContext * /*ctx*/) override { }
  virtual void exitComments(SV3_1aPpParser::CommentsContext * /*ctx*/) override { }

  virtual void enterNumber(SV3_1aPpParser::NumberContext * /*ctx*/) override { }
  virtual void exitNumber(SV3_1aPpParser::NumberContext * /*ctx*/) override { }

  virtual void enterPound_delay(SV3_1aPpParser::Pound_delayContext * /*ctx*/) override { }
  virtual void exitPound_delay(SV3_1aPpParser::Pound_delayContext * /*ctx*/) override { }

  virtual void enterPound_pound_delay(SV3_1aPpParser::Pound_pound_delayContext * /*ctx*/) override { }
  virtual void exitPound_pound_delay(SV3_1aPpParser::Pound_pound_delayContext * /*ctx*/) override { }

  virtual void enterMacro_definition(SV3_1aPpParser::Macro_definitionContext * /*ctx*/) override { }
  virtual void exitMacro_definition(SV3_1aPpParser::Macro_definitionContext * /*ctx*/) override { }

  virtual void enterInclude_directive(SV3_1aPpParser::Include_directiveContext * /*ctx*/) override { }
  virtual void exitInclude_directive(SV3_1aPpParser::Include_directiveContext * /*ctx*/) override { }

  virtual void enterLine_directive(SV3_1aPpParser::Line_directiveContext * /*ctx*/) override { }
  virtual void exitLine_directive(SV3_1aPpParser::Line_directiveContext * /*ctx*/) override { }

  virtual void enterDefault_nettype_directive(SV3_1aPpParser::Default_nettype_directiveContext * /*ctx*/) override { }
  virtual void exitDefault_nettype_directive(SV3_1aPpParser::Default_nettype_directiveContext * /*ctx*/) override { }

  virtual void enterSv_file_directive(SV3_1aPpParser::Sv_file_directiveContext * /*ctx*/) override { }
  virtual void exitSv_file_directive(SV3_1aPpParser::Sv_file_directiveContext * /*ctx*/) override { }

  virtual void enterSv_line_directive(SV3_1aPpParser::Sv_line_directiveContext * /*ctx*/) override { }
  virtual void exitSv_line_directive(SV3_1aPpParser::Sv_line_directiveContext * /*ctx*/) override { }

  virtual void enterTimescale_directive(SV3_1aPpParser::Timescale_directiveContext * /*ctx*/) override { }
  virtual void exitTimescale_directive(SV3_1aPpParser::Timescale_directiveContext * /*ctx*/) override { }

  virtual void enterUndef_directive(SV3_1aPpParser::Undef_directiveContext * /*ctx*/) override { }
  virtual void exitUndef_directive(SV3_1aPpParser::Undef_directiveContext * /*ctx*/) override { }

  virtual void enterIfdef_directive(SV3_1aPpParser::Ifdef_directiveContext * /*ctx*/) override { }
  virtual void exitIfdef_directive(SV3_1aPpParser::Ifdef_directiveContext * /*ctx*/) override { }

  virtual void enterIfdef_directive_in_macro_body(SV3_1aPpParser::Ifdef_directive_in_macro_bodyContext * /*ctx*/) override { }
  virtual void exitIfdef_directive_in_macro_body(SV3_1aPpParser::Ifdef_directive_in_macro_bodyContext * /*ctx*/) override { }

  virtual void enterIfndef_directive(SV3_1aPpParser::Ifndef_directiveContext * /*ctx*/) override { }
  virtual void exitIfndef_directive(SV3_1aPpParser::Ifndef_directiveContext * /*ctx*/) override { }

  virtual void enterIfndef_directive_in_macro_body(SV3_1aPpParser::Ifndef_directive_in_macro_bodyContext * /*ctx*/) override { }
  virtual void exitIfndef_directive_in_macro_body(SV3_1aPpParser::Ifndef_directive_in_macro_bodyContext * /*ctx*/) override { }

  virtual void enterElsif_directive(SV3_1aPpParser::Elsif_directiveContext * /*ctx*/) override { }
  virtual void exitElsif_directive(SV3_1aPpParser::Elsif_directiveContext * /*ctx*/) override { }

  virtual void enterElsif_directive_in_macro_body(SV3_1aPpParser::Elsif_directive_in_macro_bodyContext * /*ctx*/) override { }
  virtual void exitElsif_directive_in_macro_body(SV3_1aPpParser::Elsif_directive_in_macro_bodyContext * /*ctx*/) override { }

  virtual void enterElseif_directive(SV3_1aPpParser::Elseif_directiveContext * /*ctx*/) override { }
  virtual void exitElseif_directive(SV3_1aPpParser::Elseif_directiveContext * /*ctx*/) override { }

  virtual void enterElseif_directive_in_macro_body(SV3_1aPpParser::Elseif_directive_in_macro_bodyContext * /*ctx*/) override { }
  virtual void exitElseif_directive_in_macro_body(SV3_1aPpParser::Elseif_directive_in_macro_bodyContext * /*ctx*/) override { }

  virtual void enterElse_directive(SV3_1aPpParser::Else_directiveContext * /*ctx*/) override { }
  virtual void exitElse_directive(SV3_1aPpParser::Else_directiveContext * /*ctx*/) override { }

  virtual void enterEndif_directive(SV3_1aPpParser::Endif_directiveContext * /*ctx*/) override { }
  virtual void exitEndif_directive(SV3_1aPpParser::Endif_directiveContext * /*ctx*/) override { }

  virtual void enterResetall_directive(SV3_1aPpParser::Resetall_directiveContext * /*ctx*/) override { }
  virtual void exitResetall_directive(SV3_1aPpParser::Resetall_directiveContext * /*ctx*/) override { }

  virtual void enterBegin_keywords_directive(SV3_1aPpParser::Begin_keywords_directiveContext * /*ctx*/) override { }
  virtual void exitBegin_keywords_directive(SV3_1aPpParser::Begin_keywords_directiveContext * /*ctx*/) override { }

  virtual void enterEnd_keywords_directive(SV3_1aPpParser::End_keywords_directiveContext * /*ctx*/) override { }
  virtual void exitEnd_keywords_directive(SV3_1aPpParser::End_keywords_directiveContext * /*ctx*/) override { }

  virtual void enterPragma_directive(SV3_1aPpParser::Pragma_directiveContext * /*ctx*/) override { }
  virtual void exitPragma_directive(SV3_1aPpParser::Pragma_directiveContext * /*ctx*/) override { }

  virtual void enterCelldefine_directive(SV3_1aPpParser::Celldefine_directiveContext * /*ctx*/) override { }
  virtual void exitCelldefine_directive(SV3_1aPpParser::Celldefine_directiveContext * /*ctx*/) override { }

  virtual void enterEndcelldefine_directive(SV3_1aPpParser::Endcelldefine_directiveContext * /*ctx*/) override { }
  virtual void exitEndcelldefine_directive(SV3_1aPpParser::Endcelldefine_directiveContext * /*ctx*/) override { }

  virtual void enterProtect_directive(SV3_1aPpParser::Protect_directiveContext * /*ctx*/) override { }
  virtual void exitProtect_directive(SV3_1aPpParser::Protect_directiveContext * /*ctx*/) override { }

  virtual void enterEndprotect_directive(SV3_1aPpParser::Endprotect_directiveContext * /*ctx*/) override { }
  virtual void exitEndprotect_directive(SV3_1aPpParser::Endprotect_directiveContext * /*ctx*/) override { }

  virtual void enterProtected_directive(SV3_1aPpParser::Protected_directiveContext * /*ctx*/) override { }
  virtual void exitProtected_directive(SV3_1aPpParser::Protected_directiveContext * /*ctx*/) override { }

  virtual void enterEndprotected_directive(SV3_1aPpParser::Endprotected_directiveContext * /*ctx*/) override { }
  virtual void exitEndprotected_directive(SV3_1aPpParser::Endprotected_directiveContext * /*ctx*/) override { }

  virtual void enterExpand_vectornets_directive(SV3_1aPpParser::Expand_vectornets_directiveContext * /*ctx*/) override { }
  virtual void exitExpand_vectornets_directive(SV3_1aPpParser::Expand_vectornets_directiveContext * /*ctx*/) override { }

  virtual void enterNoexpand_vectornets_directive(SV3_1aPpParser::Noexpand_vectornets_directiveContext * /*ctx*/) override { }
  virtual void exitNoexpand_vectornets_directive(SV3_1aPpParser::Noexpand_vectornets_directiveContext * /*ctx*/) override { }

  virtual void enterAutoexpand_vectornets_directive(SV3_1aPpParser::Autoexpand_vectornets_directiveContext * /*ctx*/) override { }
  virtual void exitAutoexpand_vectornets_directive(SV3_1aPpParser::Autoexpand_vectornets_directiveContext * /*ctx*/) override { }

  virtual void enterUselib_directive(SV3_1aPpParser::Uselib_directiveContext * /*ctx*/) override { }
  virtual void exitUselib_directive(SV3_1aPpParser::Uselib_directiveContext * /*ctx*/) override { }

  virtual void enterDisable_portfaults_directive(SV3_1aPpParser::Disable_portfaults_directiveContext * /*ctx*/) override { }
  virtual void exitDisable_portfaults_directive(SV3_1aPpParser::Disable_portfaults_directiveContext * /*ctx*/) override { }

  virtual void enterEnable_portfaults_directive(SV3_1aPpParser::Enable_portfaults_directiveContext * /*ctx*/) override { }
  virtual void exitEnable_portfaults_directive(SV3_1aPpParser::Enable_portfaults_directiveContext * /*ctx*/) override { }

  virtual void enterNosuppress_faults_directive(SV3_1aPpParser::Nosuppress_faults_directiveContext * /*ctx*/) override { }
  virtual void exitNosuppress_faults_directive(SV3_1aPpParser::Nosuppress_faults_directiveContext * /*ctx*/) override { }

  virtual void enterSuppress_faults_directive(SV3_1aPpParser::Suppress_faults_directiveContext * /*ctx*/) override { }
  virtual void exitSuppress_faults_directive(SV3_1aPpParser::Suppress_faults_directiveContext * /*ctx*/) override { }

  virtual void enterSigned_directive(SV3_1aPpParser::Signed_directiveContext * /*ctx*/) override { }
  virtual void exitSigned_directive(SV3_1aPpParser::Signed_directiveContext * /*ctx*/) override { }

  virtual void enterUnsigned_directive(SV3_1aPpParser::Unsigned_directiveContext * /*ctx*/) override { }
  virtual void exitUnsigned_directive(SV3_1aPpParser::Unsigned_directiveContext * /*ctx*/) override { }

  virtual void enterRemove_gatename_directive(SV3_1aPpParser::Remove_gatename_directiveContext * /*ctx*/) override { }
  virtual void exitRemove_gatename_directive(SV3_1aPpParser::Remove_gatename_directiveContext * /*ctx*/) override { }

  virtual void enterNoremove_gatenames_directive(SV3_1aPpParser::Noremove_gatenames_directiveContext * /*ctx*/) override { }
  virtual void exitNoremove_gatenames_directive(SV3_1aPpParser::Noremove_gatenames_directiveContext * /*ctx*/) override { }

  virtual void enterRemove_netname_directive(SV3_1aPpParser::Remove_netname_directiveContext * /*ctx*/) override { }
  virtual void exitRemove_netname_directive(SV3_1aPpParser::Remove_netname_directiveContext * /*ctx*/) override { }

  virtual void enterNoremove_netnames_directive(SV3_1aPpParser::Noremove_netnames_directiveContext * /*ctx*/) override { }
  virtual void exitNoremove_netnames_directive(SV3_1aPpParser::Noremove_netnames_directiveContext * /*ctx*/) override { }

  virtual void enterAccelerate_directive(SV3_1aPpParser::Accelerate_directiveContext * /*ctx*/) override { }
  virtual void exitAccelerate_directive(SV3_1aPpParser::Accelerate_directiveContext * /*ctx*/) override { }

  virtual void enterNoaccelerate_directive(SV3_1aPpParser::Noaccelerate_directiveContext * /*ctx*/) override { }
  virtual void exitNoaccelerate_directive(SV3_1aPpParser::Noaccelerate_directiveContext * /*ctx*/) override { }

  virtual void enterDefault_trireg_strenght_directive(SV3_1aPpParser::Default_trireg_strenght_directiveContext * /*ctx*/) override { }
  virtual void exitDefault_trireg_strenght_directive(SV3_1aPpParser::Default_trireg_strenght_directiveContext * /*ctx*/) override { }

  virtual void enterDefault_decay_time_directive(SV3_1aPpParser::Default_decay_time_directiveContext * /*ctx*/) override { }
  virtual void exitDefault_decay_time_directive(SV3_1aPpParser::Default_decay_time_directiveContext * /*ctx*/) override { }

  virtual void enterUnconnected_drive_directive(SV3_1aPpParser::Unconnected_drive_directiveContext * /*ctx*/) override { }
  virtual void exitUnconnected_drive_directive(SV3_1aPpParser::Unconnected_drive_directiveContext * /*ctx*/) override { }

  virtual void enterNounconnected_drive_directive(SV3_1aPpParser::Nounconnected_drive_directiveContext * /*ctx*/) override { }
  virtual void exitNounconnected_drive_directive(SV3_1aPpParser::Nounconnected_drive_directiveContext * /*ctx*/) override { }

  virtual void enterDelay_mode_distributed_directive(SV3_1aPpParser::Delay_mode_distributed_directiveContext * /*ctx*/) override { }
  virtual void exitDelay_mode_distributed_directive(SV3_1aPpParser::Delay_mode_distributed_directiveContext * /*ctx*/) override { }

  virtual void enterDelay_mode_path_directive(SV3_1aPpParser::Delay_mode_path_directiveContext * /*ctx*/) override { }
  virtual void exitDelay_mode_path_directive(SV3_1aPpParser::Delay_mode_path_directiveContext * /*ctx*/) override { }

  virtual void enterDelay_mode_unit_directive(SV3_1aPpParser::Delay_mode_unit_directiveContext * /*ctx*/) override { }
  virtual void exitDelay_mode_unit_directive(SV3_1aPpParser::Delay_mode_unit_directiveContext * /*ctx*/) override { }

  virtual void enterDelay_mode_zero_directive(SV3_1aPpParser::Delay_mode_zero_directiveContext * /*ctx*/) override { }
  virtual void exitDelay_mode_zero_directive(SV3_1aPpParser::Delay_mode_zero_directiveContext * /*ctx*/) override { }

  virtual void enterUndefineall_directive(SV3_1aPpParser::Undefineall_directiveContext * /*ctx*/) override { }
  virtual void exitUndefineall_directive(SV3_1aPpParser::Undefineall_directiveContext * /*ctx*/) override { }

  virtual void enterModule(SV3_1aPpParser::ModuleContext * /*ctx*/) override { }
  virtual void exitModule(SV3_1aPpParser::ModuleContext * /*ctx*/) override { }

  virtual void enterEndmodule(SV3_1aPpParser::EndmoduleContext * /*ctx*/) override { }
  virtual void exitEndmodule(SV3_1aPpParser::EndmoduleContext * /*ctx*/) override { }

  virtual void enterSv_interface(SV3_1aPpParser::Sv_interfaceContext * /*ctx*/) override { }
  virtual void exitSv_interface(SV3_1aPpParser::Sv_interfaceContext * /*ctx*/) override { }

  virtual void enterEndinterface(SV3_1aPpParser::EndinterfaceContext * /*ctx*/) override { }
  virtual void exitEndinterface(SV3_1aPpParser::EndinterfaceContext * /*ctx*/) override { }

  virtual void enterProgram(SV3_1aPpParser::ProgramContext * /*ctx*/) override { }
  virtual void exitProgram(SV3_1aPpParser::ProgramContext * /*ctx*/) override { }

  virtual void enterEndprogram(SV3_1aPpParser::EndprogramContext * /*ctx*/) override { }
  virtual void exitEndprogram(SV3_1aPpParser::EndprogramContext * /*ctx*/) override { }

  virtual void enterPrimitive(SV3_1aPpParser::PrimitiveContext * /*ctx*/) override { }
  virtual void exitPrimitive(SV3_1aPpParser::PrimitiveContext * /*ctx*/) override { }

  virtual void enterEndprimitive(SV3_1aPpParser::EndprimitiveContext * /*ctx*/) override { }
  virtual void exitEndprimitive(SV3_1aPpParser::EndprimitiveContext * /*ctx*/) override { }

  virtual void enterSv_package(SV3_1aPpParser::Sv_packageContext * /*ctx*/) override { }
  virtual void exitSv_package(SV3_1aPpParser::Sv_packageContext * /*ctx*/) override { }

  virtual void enterEndpackage(SV3_1aPpParser::EndpackageContext * /*ctx*/) override { }
  virtual void exitEndpackage(SV3_1aPpParser::EndpackageContext * /*ctx*/) override { }

  virtual void enterChecker(SV3_1aPpParser::CheckerContext * /*ctx*/) override { }
  virtual void exitChecker(SV3_1aPpParser::CheckerContext * /*ctx*/) override { }

  virtual void enterEndchecker(SV3_1aPpParser::EndcheckerContext * /*ctx*/) override { }
  virtual void exitEndchecker(SV3_1aPpParser::EndcheckerContext * /*ctx*/) override { }

  virtual void enterConfig(SV3_1aPpParser::ConfigContext * /*ctx*/) override { }
  virtual void exitConfig(SV3_1aPpParser::ConfigContext * /*ctx*/) override { }

  virtual void enterEndconfig(SV3_1aPpParser::EndconfigContext * /*ctx*/) override { }
  virtual void exitEndconfig(SV3_1aPpParser::EndconfigContext * /*ctx*/) override { }

  virtual void enterDefine_directive(SV3_1aPpParser::Define_directiveContext * /*ctx*/) override { }
  virtual void exitDefine_directive(SV3_1aPpParser::Define_directiveContext * /*ctx*/) override { }

  virtual void enterMultiline_no_args_macro_definition(SV3_1aPpParser::Multiline_no_args_macro_definitionContext * /*ctx*/) override { }
  virtual void exitMultiline_no_args_macro_definition(SV3_1aPpParser::Multiline_no_args_macro_definitionContext * /*ctx*/) override { }

  virtual void enterMultiline_args_macro_definition(SV3_1aPpParser::Multiline_args_macro_definitionContext * /*ctx*/) override { }
  virtual void exitMultiline_args_macro_definition(SV3_1aPpParser::Multiline_args_macro_definitionContext * /*ctx*/) override { }

  virtual void enterSimple_no_args_macro_definition(SV3_1aPpParser::Simple_no_args_macro_definitionContext * /*ctx*/) override { }
  virtual void exitSimple_no_args_macro_definition(SV3_1aPpParser::Simple_no_args_macro_definitionContext * /*ctx*/) override { }

  virtual void enterSimple_args_macro_definition(SV3_1aPpParser::Simple_args_macro_definitionContext * /*ctx*/) override { }
  virtual void exitSimple_args_macro_definition(SV3_1aPpParser::Simple_args_macro_definitionContext * /*ctx*/) override { }

  virtual void enterIdentifier_in_macro_body(SV3_1aPpParser::Identifier_in_macro_bodyContext * /*ctx*/) override { }
  virtual void exitIdentifier_in_macro_body(SV3_1aPpParser::Identifier_in_macro_bodyContext * /*ctx*/) override { }

  virtual void enterSimple_no_args_macro_definition_in_macro_body(SV3_1aPpParser::Simple_no_args_macro_definition_in_macro_bodyContext * /*ctx*/) override { }
  virtual void exitSimple_no_args_macro_definition_in_macro_body(SV3_1aPpParser::Simple_no_args_macro_definition_in_macro_bodyContext * /*ctx*/) override { }

  virtual void enterSimple_args_macro_definition_in_macro_body(SV3_1aPpParser::Simple_args_macro_definition_in_macro_bodyContext * /*ctx*/) override { }
  virtual void exitSimple_args_macro_definition_in_macro_body(SV3_1aPpParser::Simple_args_macro_definition_in_macro_bodyContext * /*ctx*/) override { }

  virtual void enterDirective_in_macro(SV3_1aPpParser::Directive_in_macroContext * /*ctx*/) override { }
  virtual void exitDirective_in_macro(SV3_1aPpParser::Directive_in_macroContext * /*ctx*/) override { }

  virtual void enterMacro_arguments(SV3_1aPpParser::Macro_argumentsContext * /*ctx*/) override { }
  virtual void exitMacro_arguments(SV3_1aPpParser::Macro_argumentsContext * /*ctx*/) override { }

  virtual void enterEscaped_macro_definition_body(SV3_1aPpParser::Escaped_macro_definition_bodyContext * /*ctx*/) override { }
  virtual void exitEscaped_macro_definition_body(SV3_1aPpParser::Escaped_macro_definition_bodyContext * /*ctx*/) override { }

  virtual void enterEscaped_macro_definition_body_alt1(SV3_1aPpParser::Escaped_macro_definition_body_alt1Context * /*ctx*/) override { }
  virtual void exitEscaped_macro_definition_body_alt1(SV3_1aPpParser::Escaped_macro_definition_body_alt1Context * /*ctx*/) override { }

  virtual void enterEscaped_macro_definition_body_alt2(SV3_1aPpParser::Escaped_macro_definition_body_alt2Context * /*ctx*/) override { }
  virtual void exitEscaped_macro_definition_body_alt2(SV3_1aPpParser::Escaped_macro_definition_body_alt2Context * /*ctx*/) override { }

  virtual void enterSimple_macro_definition_body(SV3_1aPpParser::Simple_macro_definition_bodyContext * /*ctx*/) override { }
  virtual void exitSimple_macro_definition_body(SV3_1aPpParser::Simple_macro_definition_bodyContext * /*ctx*/) override { }

  virtual void enterSimple_macro_definition_body_in_macro_body(SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext * /*ctx*/) override { }
  virtual void exitSimple_macro_definition_body_in_macro_body(SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext * /*ctx*/) override { }

  virtual void enterPragma_expression(SV3_1aPpParser::Pragma_expressionContext * /*ctx*/) override { }
  virtual void exitPragma_expression(SV3_1aPpParser::Pragma_expressionContext * /*ctx*/) override { }

  virtual void enterMacro_arg(SV3_1aPpParser::Macro_argContext * /*ctx*/) override { }
  virtual void exitMacro_arg(SV3_1aPpParser::Macro_argContext * /*ctx*/) override { }

  virtual void enterPaired_parens(SV3_1aPpParser::Paired_parensContext * /*ctx*/) override { }
  virtual void exitPaired_parens(SV3_1aPpParser::Paired_parensContext * /*ctx*/) override { }

  virtual void enterText_blob(SV3_1aPpParser::Text_blobContext * /*ctx*/) override { }
  virtual void exitText_blob(SV3_1aPpParser::Text_blobContext * /*ctx*/) override { }

  virtual void enterString(SV3_1aPpParser::StringContext * /*ctx*/) override { }
  virtual void exitString(SV3_1aPpParser::StringContext * /*ctx*/) override { }

  virtual void enterEscaped_identifier(SV3_1aPpParser::Escaped_identifierContext * /*ctx*/) override { }
  virtual void exitEscaped_identifier(SV3_1aPpParser::Escaped_identifierContext * /*ctx*/) override { }

  virtual void enterDefault_value(SV3_1aPpParser::Default_valueContext * /*ctx*/) override { }
  virtual void exitDefault_value(SV3_1aPpParser::Default_valueContext * /*ctx*/) override { }

  virtual void enterString_blob(SV3_1aPpParser::String_blobContext * /*ctx*/) override { }
  virtual void exitString_blob(SV3_1aPpParser::String_blobContext * /*ctx*/) override { }


  virtual void enterEveryRule(antlr4::ParserRuleContext * /*ctx*/) override { }
  virtual void exitEveryRule(antlr4::ParserRuleContext * /*ctx*/) override { }
  virtual void visitTerminal(antlr4::tree::TerminalNode * /*node*/) override { }
  virtual void visitErrorNode(antlr4::tree::ErrorNode * /*node*/) override { }

};

