
// Generated from SV3_1aPpParser.g4 by ANTLR 4.9.2

#pragma once


#include "antlr4-runtime.h"




class  SV3_1aPpParser : public antlr4::Parser {
  IMPLEMENT_RTTI(SV3_1aPpParser, antlr4::Parser)
public:
  enum {
    Escaped_identifier = 1, One_line_comment = 2, Block_comment = 3, TICK_VARIABLE = 4, 
    TICK_DEFINE = 5, TICK_CELLDEFINE = 6, TICK_ENDCELLDEFINE = 7, TICK_DEFAULT_NETTYPE = 8, 
    TICK_UNDEF = 9, TICK_IFDEF = 10, TICK_IFNDEF = 11, TICK_ELSE = 12, TICK_ELSIF = 13, 
    TICK_ELSEIF = 14, TICK_ENDIF = 15, TICK_INCLUDE = 16, TICK_PRAGMA = 17, 
    TICK_BEGIN_KEYWORDS = 18, TICK_END_KEYWORDS = 19, TICK_RESETALL = 20, 
    TICK_TIMESCALE = 21, TICK_UNCONNECTED_DRIVE = 22, TICK_NOUNCONNECTED_DRIVE = 23, 
    TICK_LINE = 24, TICK_DEFAULT_DECAY_TIME = 25, TICK_DEFAULT_TRIREG_STRENGTH = 26, 
    TICK_DELAY_MODE_DISTRIBUTED = 27, TICK_DELAY_MODE_PATH = 28, TICK_DELAY_MODE_UNIT = 29, 
    TICK_DELAY_MODE_ZERO = 30, TICK_UNDEFINEALL = 31, TICK_ACCELERATE = 32, 
    TICK_NOACCELERATE = 33, TICK_PROTECT = 34, TICK_USELIB = 35, TICK_DISABLE_PORTFAULTS = 36, 
    TICK_ENABLE_PORTFAULTS = 37, TICK_NOSUPPRESS_FAULTS = 38, TICK_SUPPRESS_FAULTS = 39, 
    TICK_SIGNED = 40, TICK_UNSIGNED = 41, TICK_ENDPROTECT = 42, TICK_PROTECTED = 43, 
    TICK_ENDPROTECTED = 44, TICK_EXPAND_VECTORNETS = 45, TICK_NOEXPAND_VECTORNETS = 46, 
    TICK_AUTOEXPAND_VECTORNETS = 47, TICK_REMOVE_GATENAME = 48, TICK_NOREMOVE_GATENAMES = 49, 
    TICK_REMOVE_NETNAME = 50, TICK_NOREMOVE_NETNAMES = 51, TICK_FILE__ = 52, 
    TICK_LINE__ = 53, MODULE = 54, ENDMODULE = 55, INTERFACE = 56, ENDINTERFACE = 57, 
    PROGRAM = 58, ENDPROGRAM = 59, PRIMITIVE = 60, ENDPRIMITIVE = 61, PACKAGE = 62, 
    ENDPACKAGE = 63, CHECKER = 64, ENDCHECKER = 65, CONFIG = 66, ENDCONFIG = 67, 
    Macro_identifier = 68, Macro_Escaped_identifier = 69, String = 70, Simple_identifier = 71, 
    Spaces = 72, Pound_Pound_delay = 73, Pound_delay = 74, TIMESCALE = 75, 
    Number = 76, Fixed_point_number = 77, TEXT_CR = 78, ESCAPED_CR = 79, 
    CR = 80, TICK_QUOTE = 81, TICK_BACKSLASH_TICK_QUOTE = 82, TICK_TICK = 83, 
    PARENS_OPEN = 84, PARENS_CLOSE = 85, COMMA = 86, EQUAL_OP = 87, DOUBLE_QUOTE = 88, 
    CURLY_OPEN = 89, CURLY_CLOSE = 90, SQUARE_OPEN = 91, SQUARE_CLOSE = 92, 
    Special = 93, ANY = 94
  };

  enum {
    RuleTop_level_rule = 0, RuleSource_text = 1, RuleNull_rule = 2, RuleDescription = 3, 
    RuleEscaped_identifier = 4, RuleMacro_instance = 5, RuleUnterminated_string = 6, 
    RuleMacro_actual_args = 7, RuleComments = 8, RuleNumber = 9, RulePound_delay = 10, 
    RulePound_pound_delay = 11, RuleMacro_definition = 12, RuleInclude_directive = 13, 
    RuleLine_directive = 14, RuleDefault_nettype_directive = 15, RuleSv_file_directive = 16, 
    RuleSv_line_directive = 17, RuleTimescale_directive = 18, RuleUndef_directive = 19, 
    RuleIfdef_directive = 20, RuleIfdef_directive_in_macro_body = 21, RuleIfndef_directive = 22, 
    RuleIfndef_directive_in_macro_body = 23, RuleElsif_directive = 24, RuleElsif_directive_in_macro_body = 25, 
    RuleElseif_directive = 26, RuleElseif_directive_in_macro_body = 27, 
    RuleElse_directive = 28, RuleEndif_directive = 29, RuleResetall_directive = 30, 
    RuleBegin_keywords_directive = 31, RuleEnd_keywords_directive = 32, 
    RulePragma_directive = 33, RuleCelldefine_directive = 34, RuleEndcelldefine_directive = 35, 
    RuleProtect_directive = 36, RuleEndprotect_directive = 37, RuleProtected_directive = 38, 
    RuleEndprotected_directive = 39, RuleExpand_vectornets_directive = 40, 
    RuleNoexpand_vectornets_directive = 41, RuleAutoexpand_vectornets_directive = 42, 
    RuleUselib_directive = 43, RuleDisable_portfaults_directive = 44, RuleEnable_portfaults_directive = 45, 
    RuleNosuppress_faults_directive = 46, RuleSuppress_faults_directive = 47, 
    RuleSigned_directive = 48, RuleUnsigned_directive = 49, RuleRemove_gatename_directive = 50, 
    RuleNoremove_gatenames_directive = 51, RuleRemove_netname_directive = 52, 
    RuleNoremove_netnames_directive = 53, RuleAccelerate_directive = 54, 
    RuleNoaccelerate_directive = 55, RuleDefault_trireg_strenght_directive = 56, 
    RuleDefault_decay_time_directive = 57, RuleUnconnected_drive_directive = 58, 
    RuleNounconnected_drive_directive = 59, RuleDelay_mode_distributed_directive = 60, 
    RuleDelay_mode_path_directive = 61, RuleDelay_mode_unit_directive = 62, 
    RuleDelay_mode_zero_directive = 63, RuleUndefineall_directive = 64, 
    RuleModule = 65, RuleEndmodule = 66, RuleSv_interface = 67, RuleEndinterface = 68, 
    RuleProgram = 69, RuleEndprogram = 70, RulePrimitive = 71, RuleEndprimitive = 72, 
    RuleSv_package = 73, RuleEndpackage = 74, RuleChecker = 75, RuleEndchecker = 76, 
    RuleConfig = 77, RuleEndconfig = 78, RuleDefine_directive = 79, RuleMultiline_no_args_macro_definition = 80, 
    RuleMultiline_args_macro_definition = 81, RuleSimple_no_args_macro_definition = 82, 
    RuleSimple_args_macro_definition = 83, RuleIdentifier_in_macro_body = 84, 
    RuleSimple_no_args_macro_definition_in_macro_body = 85, RuleSimple_args_macro_definition_in_macro_body = 86, 
    RuleDirective_in_macro = 87, RuleMacro_arguments = 88, RuleEscaped_macro_definition_body = 89, 
    RuleEscaped_macro_definition_body_alt1 = 90, RuleEscaped_macro_definition_body_alt2 = 91, 
    RuleSimple_macro_definition_body = 92, RuleSimple_macro_definition_body_in_macro_body = 93, 
    RulePragma_expression = 94, RuleMacro_arg = 95, RulePaired_parens = 96, 
    RuleText_blob = 97, RuleString = 98, RuleDefault_value = 99, RuleString_blob = 100
  };

  explicit SV3_1aPpParser(antlr4::TokenStream *input);
  ~SV3_1aPpParser();

  virtual std::string getGrammarFileName() const override;
  virtual const antlr4::atn::ATN& getATN() const override { return _atn; };
  virtual const std::vector<std::string>& getTokenNames() const override { return _tokenNames; }; // deprecated: use vocabulary instead.
  virtual const std::vector<std::string>& getRuleNames() const override;
  virtual antlr4::dfa::Vocabulary& getVocabulary() const override;


  class Top_level_ruleContext;
  class Source_textContext;
  class Null_ruleContext;
  class DescriptionContext;
  class Escaped_identifierContext;
  class Macro_instanceContext;
  class Unterminated_stringContext;
  class Macro_actual_argsContext;
  class CommentsContext;
  class NumberContext;
  class Pound_delayContext;
  class Pound_pound_delayContext;
  class Macro_definitionContext;
  class Include_directiveContext;
  class Line_directiveContext;
  class Default_nettype_directiveContext;
  class Sv_file_directiveContext;
  class Sv_line_directiveContext;
  class Timescale_directiveContext;
  class Undef_directiveContext;
  class Ifdef_directiveContext;
  class Ifdef_directive_in_macro_bodyContext;
  class Ifndef_directiveContext;
  class Ifndef_directive_in_macro_bodyContext;
  class Elsif_directiveContext;
  class Elsif_directive_in_macro_bodyContext;
  class Elseif_directiveContext;
  class Elseif_directive_in_macro_bodyContext;
  class Else_directiveContext;
  class Endif_directiveContext;
  class Resetall_directiveContext;
  class Begin_keywords_directiveContext;
  class End_keywords_directiveContext;
  class Pragma_directiveContext;
  class Celldefine_directiveContext;
  class Endcelldefine_directiveContext;
  class Protect_directiveContext;
  class Endprotect_directiveContext;
  class Protected_directiveContext;
  class Endprotected_directiveContext;
  class Expand_vectornets_directiveContext;
  class Noexpand_vectornets_directiveContext;
  class Autoexpand_vectornets_directiveContext;
  class Uselib_directiveContext;
  class Disable_portfaults_directiveContext;
  class Enable_portfaults_directiveContext;
  class Nosuppress_faults_directiveContext;
  class Suppress_faults_directiveContext;
  class Signed_directiveContext;
  class Unsigned_directiveContext;
  class Remove_gatename_directiveContext;
  class Noremove_gatenames_directiveContext;
  class Remove_netname_directiveContext;
  class Noremove_netnames_directiveContext;
  class Accelerate_directiveContext;
  class Noaccelerate_directiveContext;
  class Default_trireg_strenght_directiveContext;
  class Default_decay_time_directiveContext;
  class Unconnected_drive_directiveContext;
  class Nounconnected_drive_directiveContext;
  class Delay_mode_distributed_directiveContext;
  class Delay_mode_path_directiveContext;
  class Delay_mode_unit_directiveContext;
  class Delay_mode_zero_directiveContext;
  class Undefineall_directiveContext;
  class ModuleContext;
  class EndmoduleContext;
  class Sv_interfaceContext;
  class EndinterfaceContext;
  class ProgramContext;
  class EndprogramContext;
  class PrimitiveContext;
  class EndprimitiveContext;
  class Sv_packageContext;
  class EndpackageContext;
  class CheckerContext;
  class EndcheckerContext;
  class ConfigContext;
  class EndconfigContext;
  class Define_directiveContext;
  class Multiline_no_args_macro_definitionContext;
  class Multiline_args_macro_definitionContext;
  class Simple_no_args_macro_definitionContext;
  class Simple_args_macro_definitionContext;
  class Identifier_in_macro_bodyContext;
  class Simple_no_args_macro_definition_in_macro_bodyContext;
  class Simple_args_macro_definition_in_macro_bodyContext;
  class Directive_in_macroContext;
  class Macro_argumentsContext;
  class Escaped_macro_definition_bodyContext;
  class Escaped_macro_definition_body_alt1Context;
  class Escaped_macro_definition_body_alt2Context;
  class Simple_macro_definition_bodyContext;
  class Simple_macro_definition_body_in_macro_bodyContext;
  class Pragma_expressionContext;
  class Macro_argContext;
  class Paired_parensContext;
  class Text_blobContext;
  class StringContext;
  class Default_valueContext;
  class String_blobContext; 

  class  Top_level_ruleContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Top_level_ruleContext, antlr4::ParserRuleContext)
  public:
    Top_level_ruleContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Null_ruleContext *null_rule();
    Source_textContext *source_text();
    antlr4::tree::TerminalNode *EOF();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Top_level_ruleContext* top_level_rule();

  class  Source_textContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Source_textContext, antlr4::ParserRuleContext)
  public:
    Source_textContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<DescriptionContext *> description();
    DescriptionContext* description(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Source_textContext* source_text();

  class  Null_ruleContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Null_ruleContext, antlr4::ParserRuleContext)
  public:
    Null_ruleContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Null_ruleContext* null_rule();

  class  DescriptionContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(DescriptionContext, antlr4::ParserRuleContext)
  public:
    DescriptionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Escaped_identifierContext *escaped_identifier();
    Unterminated_stringContext *unterminated_string();
    StringContext *string();
    NumberContext *number();
    Macro_definitionContext *macro_definition();
    CommentsContext *comments();
    Celldefine_directiveContext *celldefine_directive();
    Endcelldefine_directiveContext *endcelldefine_directive();
    Default_nettype_directiveContext *default_nettype_directive();
    Undef_directiveContext *undef_directive();
    Ifdef_directiveContext *ifdef_directive();
    Ifndef_directiveContext *ifndef_directive();
    Else_directiveContext *else_directive();
    Elsif_directiveContext *elsif_directive();
    Elseif_directiveContext *elseif_directive();
    Endif_directiveContext *endif_directive();
    Include_directiveContext *include_directive();
    Resetall_directiveContext *resetall_directive();
    Begin_keywords_directiveContext *begin_keywords_directive();
    End_keywords_directiveContext *end_keywords_directive();
    Timescale_directiveContext *timescale_directive();
    Unconnected_drive_directiveContext *unconnected_drive_directive();
    Nounconnected_drive_directiveContext *nounconnected_drive_directive();
    Line_directiveContext *line_directive();
    Default_decay_time_directiveContext *default_decay_time_directive();
    Default_trireg_strenght_directiveContext *default_trireg_strenght_directive();
    Delay_mode_distributed_directiveContext *delay_mode_distributed_directive();
    Delay_mode_path_directiveContext *delay_mode_path_directive();
    Delay_mode_unit_directiveContext *delay_mode_unit_directive();
    Delay_mode_zero_directiveContext *delay_mode_zero_directive();
    Protect_directiveContext *protect_directive();
    Endprotect_directiveContext *endprotect_directive();
    Protected_directiveContext *protected_directive();
    Endprotected_directiveContext *endprotected_directive();
    Expand_vectornets_directiveContext *expand_vectornets_directive();
    Noexpand_vectornets_directiveContext *noexpand_vectornets_directive();
    Autoexpand_vectornets_directiveContext *autoexpand_vectornets_directive();
    Remove_gatename_directiveContext *remove_gatename_directive();
    Noremove_gatenames_directiveContext *noremove_gatenames_directive();
    Remove_netname_directiveContext *remove_netname_directive();
    Noremove_netnames_directiveContext *noremove_netnames_directive();
    Accelerate_directiveContext *accelerate_directive();
    Noaccelerate_directiveContext *noaccelerate_directive();
    Undefineall_directiveContext *undefineall_directive();
    Uselib_directiveContext *uselib_directive();
    Disable_portfaults_directiveContext *disable_portfaults_directive();
    Enable_portfaults_directiveContext *enable_portfaults_directive();
    Nosuppress_faults_directiveContext *nosuppress_faults_directive();
    Suppress_faults_directiveContext *suppress_faults_directive();
    Signed_directiveContext *signed_directive();
    Unsigned_directiveContext *unsigned_directive();
    Pragma_directiveContext *pragma_directive();
    Sv_file_directiveContext *sv_file_directive();
    Sv_line_directiveContext *sv_line_directive();
    Macro_instanceContext *macro_instance();
    ModuleContext *module();
    EndmoduleContext *endmodule();
    Sv_interfaceContext *sv_interface();
    EndinterfaceContext *endinterface();
    ProgramContext *program();
    EndprogramContext *endprogram();
    PrimitiveContext *primitive();
    EndprimitiveContext *endprimitive();
    Sv_packageContext *sv_package();
    EndpackageContext *endpackage();
    CheckerContext *checker();
    EndcheckerContext *endchecker();
    ConfigContext *config();
    EndconfigContext *endconfig();
    Text_blobContext *text_blob();
    Pound_delayContext *pound_delay();
    Pound_pound_delayContext *pound_pound_delay();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  DescriptionContext* description();

  class  Escaped_identifierContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Escaped_identifierContext, antlr4::ParserRuleContext)
  public:
    Escaped_identifierContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Escaped_identifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Escaped_identifierContext* escaped_identifier();

  class  Macro_instanceContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Macro_instanceContext, antlr4::ParserRuleContext)
  public:
    Macro_instanceContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Macro_instanceContext() = default;
    void copyFrom(Macro_instanceContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  MacroInstanceWithArgsContext : public Macro_instanceContext {
    IMPLEMENT_RTTI(MacroInstanceWithArgsContext, Macro_instanceContext)
  public:
    MacroInstanceWithArgsContext(Macro_instanceContext *ctx);

    antlr4::tree::TerminalNode *PARENS_OPEN();
    Macro_actual_argsContext *macro_actual_args();
    antlr4::tree::TerminalNode *PARENS_CLOSE();
    antlr4::tree::TerminalNode *Macro_identifier();
    antlr4::tree::TerminalNode *Macro_Escaped_identifier();
    std::vector<antlr4::tree::TerminalNode *> Spaces();
    antlr4::tree::TerminalNode* Spaces(size_t i);
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  MacroInstanceNoArgsContext : public Macro_instanceContext {
    IMPLEMENT_RTTI(MacroInstanceNoArgsContext, Macro_instanceContext)
  public:
    MacroInstanceNoArgsContext(Macro_instanceContext *ctx);

    antlr4::tree::TerminalNode *Macro_identifier();
    antlr4::tree::TerminalNode *Macro_Escaped_identifier();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Macro_instanceContext* macro_instance();

  class  Unterminated_stringContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Unterminated_stringContext, antlr4::ParserRuleContext)
  public:
    Unterminated_stringContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *DOUBLE_QUOTE();
    antlr4::tree::TerminalNode *CR();
    std::vector<String_blobContext *> string_blob();
    String_blobContext* string_blob(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Unterminated_stringContext* unterminated_string();

  class  Macro_actual_argsContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Macro_actual_argsContext, antlr4::ParserRuleContext)
  public:
    Macro_actual_argsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Macro_argContext *> macro_arg();
    Macro_argContext* macro_arg(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Macro_actual_argsContext* macro_actual_args();

  class  CommentsContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(CommentsContext, antlr4::ParserRuleContext)
  public:
    CommentsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *One_line_comment();
    antlr4::tree::TerminalNode *Block_comment();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  CommentsContext* comments();

  class  NumberContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(NumberContext, antlr4::ParserRuleContext)
  public:
    NumberContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Number();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  NumberContext* number();

  class  Pound_delayContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Pound_delayContext, antlr4::ParserRuleContext)
  public:
    Pound_delayContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Pound_delay();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Pound_delayContext* pound_delay();

  class  Pound_pound_delayContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Pound_pound_delayContext, antlr4::ParserRuleContext)
  public:
    Pound_pound_delayContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Pound_Pound_delay();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Pound_pound_delayContext* pound_pound_delay();

  class  Macro_definitionContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Macro_definitionContext, antlr4::ParserRuleContext)
  public:
    Macro_definitionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Define_directiveContext *define_directive();
    Multiline_args_macro_definitionContext *multiline_args_macro_definition();
    Simple_no_args_macro_definitionContext *simple_no_args_macro_definition();
    Multiline_no_args_macro_definitionContext *multiline_no_args_macro_definition();
    Simple_args_macro_definitionContext *simple_args_macro_definition();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Macro_definitionContext* macro_definition();

  class  Include_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Include_directiveContext, antlr4::ParserRuleContext)
  public:
    Include_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_INCLUDE();
    antlr4::tree::TerminalNode *Spaces();
    antlr4::tree::TerminalNode *String();
    antlr4::tree::TerminalNode *Simple_identifier();
    antlr4::tree::TerminalNode *Escaped_identifier();
    Macro_instanceContext *macro_instance();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Include_directiveContext* include_directive();

  class  Line_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Line_directiveContext, antlr4::ParserRuleContext)
  public:
    Line_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_LINE();
    std::vector<antlr4::tree::TerminalNode *> Spaces();
    antlr4::tree::TerminalNode* Spaces(size_t i);
    std::vector<NumberContext *> number();
    NumberContext* number(size_t i);
    antlr4::tree::TerminalNode *String();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Line_directiveContext* line_directive();

  class  Default_nettype_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Default_nettype_directiveContext, antlr4::ParserRuleContext)
  public:
    Default_nettype_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_DEFAULT_NETTYPE();
    antlr4::tree::TerminalNode *Spaces();
    antlr4::tree::TerminalNode *Simple_identifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Default_nettype_directiveContext* default_nettype_directive();

  class  Sv_file_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Sv_file_directiveContext, antlr4::ParserRuleContext)
  public:
    Sv_file_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_FILE__();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Sv_file_directiveContext* sv_file_directive();

  class  Sv_line_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Sv_line_directiveContext, antlr4::ParserRuleContext)
  public:
    Sv_line_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_LINE__();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Sv_line_directiveContext* sv_line_directive();

  class  Timescale_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Timescale_directiveContext, antlr4::ParserRuleContext)
  public:
    Timescale_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_TIMESCALE();
    antlr4::tree::TerminalNode *TIMESCALE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Timescale_directiveContext* timescale_directive();

  class  Undef_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Undef_directiveContext, antlr4::ParserRuleContext)
  public:
    Undef_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_UNDEF();
    antlr4::tree::TerminalNode *Spaces();
    antlr4::tree::TerminalNode *Simple_identifier();
    antlr4::tree::TerminalNode *Escaped_identifier();
    Macro_instanceContext *macro_instance();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Undef_directiveContext* undef_directive();

  class  Ifdef_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Ifdef_directiveContext, antlr4::ParserRuleContext)
  public:
    Ifdef_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_IFDEF();
    antlr4::tree::TerminalNode *Spaces();
    antlr4::tree::TerminalNode *Simple_identifier();
    antlr4::tree::TerminalNode *Escaped_identifier();
    Macro_instanceContext *macro_instance();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Ifdef_directiveContext* ifdef_directive();

  class  Ifdef_directive_in_macro_bodyContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Ifdef_directive_in_macro_bodyContext, antlr4::ParserRuleContext)
  public:
    Ifdef_directive_in_macro_bodyContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_IFDEF();
    antlr4::tree::TerminalNode *Spaces();
    Identifier_in_macro_bodyContext *identifier_in_macro_body();
    antlr4::tree::TerminalNode *Escaped_identifier();
    Macro_instanceContext *macro_instance();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Ifdef_directive_in_macro_bodyContext* ifdef_directive_in_macro_body();

  class  Ifndef_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Ifndef_directiveContext, antlr4::ParserRuleContext)
  public:
    Ifndef_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_IFNDEF();
    antlr4::tree::TerminalNode *Spaces();
    antlr4::tree::TerminalNode *Simple_identifier();
    antlr4::tree::TerminalNode *Escaped_identifier();
    Macro_instanceContext *macro_instance();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Ifndef_directiveContext* ifndef_directive();

  class  Ifndef_directive_in_macro_bodyContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Ifndef_directive_in_macro_bodyContext, antlr4::ParserRuleContext)
  public:
    Ifndef_directive_in_macro_bodyContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_IFNDEF();
    antlr4::tree::TerminalNode *Spaces();
    Identifier_in_macro_bodyContext *identifier_in_macro_body();
    antlr4::tree::TerminalNode *Escaped_identifier();
    Macro_instanceContext *macro_instance();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Ifndef_directive_in_macro_bodyContext* ifndef_directive_in_macro_body();

  class  Elsif_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Elsif_directiveContext, antlr4::ParserRuleContext)
  public:
    Elsif_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_ELSIF();
    antlr4::tree::TerminalNode *Spaces();
    antlr4::tree::TerminalNode *Simple_identifier();
    antlr4::tree::TerminalNode *Escaped_identifier();
    Macro_instanceContext *macro_instance();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Elsif_directiveContext* elsif_directive();

  class  Elsif_directive_in_macro_bodyContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Elsif_directive_in_macro_bodyContext, antlr4::ParserRuleContext)
  public:
    Elsif_directive_in_macro_bodyContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_ELSIF();
    antlr4::tree::TerminalNode *Spaces();
    Identifier_in_macro_bodyContext *identifier_in_macro_body();
    antlr4::tree::TerminalNode *Escaped_identifier();
    Macro_instanceContext *macro_instance();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Elsif_directive_in_macro_bodyContext* elsif_directive_in_macro_body();

  class  Elseif_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Elseif_directiveContext, antlr4::ParserRuleContext)
  public:
    Elseif_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_ELSEIF();
    antlr4::tree::TerminalNode *Spaces();
    antlr4::tree::TerminalNode *Simple_identifier();
    antlr4::tree::TerminalNode *Escaped_identifier();
    Macro_instanceContext *macro_instance();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Elseif_directiveContext* elseif_directive();

  class  Elseif_directive_in_macro_bodyContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Elseif_directive_in_macro_bodyContext, antlr4::ParserRuleContext)
  public:
    Elseif_directive_in_macro_bodyContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_ELSEIF();
    antlr4::tree::TerminalNode *Spaces();
    Identifier_in_macro_bodyContext *identifier_in_macro_body();
    antlr4::tree::TerminalNode *Escaped_identifier();
    Macro_instanceContext *macro_instance();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Elseif_directive_in_macro_bodyContext* elseif_directive_in_macro_body();

  class  Else_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Else_directiveContext, antlr4::ParserRuleContext)
  public:
    Else_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_ELSE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Else_directiveContext* else_directive();

  class  Endif_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Endif_directiveContext, antlr4::ParserRuleContext)
  public:
    Endif_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_ENDIF();
    antlr4::tree::TerminalNode *One_line_comment();
    std::vector<antlr4::tree::TerminalNode *> Spaces();
    antlr4::tree::TerminalNode* Spaces(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Endif_directiveContext* endif_directive();

  class  Resetall_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Resetall_directiveContext, antlr4::ParserRuleContext)
  public:
    Resetall_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_RESETALL();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Resetall_directiveContext* resetall_directive();

  class  Begin_keywords_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Begin_keywords_directiveContext, antlr4::ParserRuleContext)
  public:
    Begin_keywords_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_BEGIN_KEYWORDS();
    antlr4::tree::TerminalNode *Spaces();
    antlr4::tree::TerminalNode *String();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Begin_keywords_directiveContext* begin_keywords_directive();

  class  End_keywords_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(End_keywords_directiveContext, antlr4::ParserRuleContext)
  public:
    End_keywords_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_END_KEYWORDS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  End_keywords_directiveContext* end_keywords_directive();

  class  Pragma_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Pragma_directiveContext, antlr4::ParserRuleContext)
  public:
    Pragma_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_PRAGMA();
    antlr4::tree::TerminalNode *Spaces();
    antlr4::tree::TerminalNode *Simple_identifier();
    std::vector<Pragma_expressionContext *> pragma_expression();
    Pragma_expressionContext* pragma_expression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Special();
    antlr4::tree::TerminalNode* Special(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Pragma_directiveContext* pragma_directive();

  class  Celldefine_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Celldefine_directiveContext, antlr4::ParserRuleContext)
  public:
    Celldefine_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_CELLDEFINE();
    antlr4::tree::TerminalNode *CR();
    std::vector<antlr4::tree::TerminalNode *> Spaces();
    antlr4::tree::TerminalNode* Spaces(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Celldefine_directiveContext* celldefine_directive();

  class  Endcelldefine_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Endcelldefine_directiveContext, antlr4::ParserRuleContext)
  public:
    Endcelldefine_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_ENDCELLDEFINE();
    antlr4::tree::TerminalNode *CR();
    std::vector<antlr4::tree::TerminalNode *> Spaces();
    antlr4::tree::TerminalNode* Spaces(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Endcelldefine_directiveContext* endcelldefine_directive();

  class  Protect_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Protect_directiveContext, antlr4::ParserRuleContext)
  public:
    Protect_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_PROTECT();
    antlr4::tree::TerminalNode *CR();
    std::vector<antlr4::tree::TerminalNode *> Spaces();
    antlr4::tree::TerminalNode* Spaces(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Protect_directiveContext* protect_directive();

  class  Endprotect_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Endprotect_directiveContext, antlr4::ParserRuleContext)
  public:
    Endprotect_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_ENDPROTECT();
    antlr4::tree::TerminalNode *CR();
    std::vector<antlr4::tree::TerminalNode *> Spaces();
    antlr4::tree::TerminalNode* Spaces(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Endprotect_directiveContext* endprotect_directive();

  class  Protected_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Protected_directiveContext, antlr4::ParserRuleContext)
  public:
    Protected_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_PROTECTED();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Protected_directiveContext* protected_directive();

  class  Endprotected_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Endprotected_directiveContext, antlr4::ParserRuleContext)
  public:
    Endprotected_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_ENDPROTECTED();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Endprotected_directiveContext* endprotected_directive();

  class  Expand_vectornets_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Expand_vectornets_directiveContext, antlr4::ParserRuleContext)
  public:
    Expand_vectornets_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_EXPAND_VECTORNETS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Expand_vectornets_directiveContext* expand_vectornets_directive();

  class  Noexpand_vectornets_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Noexpand_vectornets_directiveContext, antlr4::ParserRuleContext)
  public:
    Noexpand_vectornets_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_NOEXPAND_VECTORNETS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Noexpand_vectornets_directiveContext* noexpand_vectornets_directive();

  class  Autoexpand_vectornets_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Autoexpand_vectornets_directiveContext, antlr4::ParserRuleContext)
  public:
    Autoexpand_vectornets_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_AUTOEXPAND_VECTORNETS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Autoexpand_vectornets_directiveContext* autoexpand_vectornets_directive();

  class  Uselib_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Uselib_directiveContext, antlr4::ParserRuleContext)
  public:
    Uselib_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_USELIB();
    std::vector<Text_blobContext *> text_blob();
    Text_blobContext* text_blob(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Uselib_directiveContext* uselib_directive();

  class  Disable_portfaults_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Disable_portfaults_directiveContext, antlr4::ParserRuleContext)
  public:
    Disable_portfaults_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_DISABLE_PORTFAULTS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Disable_portfaults_directiveContext* disable_portfaults_directive();

  class  Enable_portfaults_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Enable_portfaults_directiveContext, antlr4::ParserRuleContext)
  public:
    Enable_portfaults_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_ENABLE_PORTFAULTS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Enable_portfaults_directiveContext* enable_portfaults_directive();

  class  Nosuppress_faults_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Nosuppress_faults_directiveContext, antlr4::ParserRuleContext)
  public:
    Nosuppress_faults_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_NOSUPPRESS_FAULTS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Nosuppress_faults_directiveContext* nosuppress_faults_directive();

  class  Suppress_faults_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Suppress_faults_directiveContext, antlr4::ParserRuleContext)
  public:
    Suppress_faults_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_SUPPRESS_FAULTS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Suppress_faults_directiveContext* suppress_faults_directive();

  class  Signed_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Signed_directiveContext, antlr4::ParserRuleContext)
  public:
    Signed_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_SIGNED();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Signed_directiveContext* signed_directive();

  class  Unsigned_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Unsigned_directiveContext, antlr4::ParserRuleContext)
  public:
    Unsigned_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_UNSIGNED();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Unsigned_directiveContext* unsigned_directive();

  class  Remove_gatename_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Remove_gatename_directiveContext, antlr4::ParserRuleContext)
  public:
    Remove_gatename_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_REMOVE_GATENAME();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Remove_gatename_directiveContext* remove_gatename_directive();

  class  Noremove_gatenames_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Noremove_gatenames_directiveContext, antlr4::ParserRuleContext)
  public:
    Noremove_gatenames_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_NOREMOVE_GATENAMES();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Noremove_gatenames_directiveContext* noremove_gatenames_directive();

  class  Remove_netname_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Remove_netname_directiveContext, antlr4::ParserRuleContext)
  public:
    Remove_netname_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_REMOVE_NETNAME();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Remove_netname_directiveContext* remove_netname_directive();

  class  Noremove_netnames_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Noremove_netnames_directiveContext, antlr4::ParserRuleContext)
  public:
    Noremove_netnames_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_NOREMOVE_NETNAMES();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Noremove_netnames_directiveContext* noremove_netnames_directive();

  class  Accelerate_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Accelerate_directiveContext, antlr4::ParserRuleContext)
  public:
    Accelerate_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_ACCELERATE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Accelerate_directiveContext* accelerate_directive();

  class  Noaccelerate_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Noaccelerate_directiveContext, antlr4::ParserRuleContext)
  public:
    Noaccelerate_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_NOACCELERATE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Noaccelerate_directiveContext* noaccelerate_directive();

  class  Default_trireg_strenght_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Default_trireg_strenght_directiveContext, antlr4::ParserRuleContext)
  public:
    Default_trireg_strenght_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_DEFAULT_TRIREG_STRENGTH();
    antlr4::tree::TerminalNode *Spaces();
    NumberContext *number();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Default_trireg_strenght_directiveContext* default_trireg_strenght_directive();

  class  Default_decay_time_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Default_decay_time_directiveContext, antlr4::ParserRuleContext)
  public:
    Default_decay_time_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_DEFAULT_DECAY_TIME();
    antlr4::tree::TerminalNode *Spaces();
    NumberContext *number();
    antlr4::tree::TerminalNode *Simple_identifier();
    antlr4::tree::TerminalNode *Fixed_point_number();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Default_decay_time_directiveContext* default_decay_time_directive();

  class  Unconnected_drive_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Unconnected_drive_directiveContext, antlr4::ParserRuleContext)
  public:
    Unconnected_drive_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_UNCONNECTED_DRIVE();
    antlr4::tree::TerminalNode *Spaces();
    antlr4::tree::TerminalNode *Simple_identifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Unconnected_drive_directiveContext* unconnected_drive_directive();

  class  Nounconnected_drive_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Nounconnected_drive_directiveContext, antlr4::ParserRuleContext)
  public:
    Nounconnected_drive_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_NOUNCONNECTED_DRIVE();
    antlr4::tree::TerminalNode *CR();
    std::vector<antlr4::tree::TerminalNode *> Spaces();
    antlr4::tree::TerminalNode* Spaces(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Nounconnected_drive_directiveContext* nounconnected_drive_directive();

  class  Delay_mode_distributed_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Delay_mode_distributed_directiveContext, antlr4::ParserRuleContext)
  public:
    Delay_mode_distributed_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_DELAY_MODE_DISTRIBUTED();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Delay_mode_distributed_directiveContext* delay_mode_distributed_directive();

  class  Delay_mode_path_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Delay_mode_path_directiveContext, antlr4::ParserRuleContext)
  public:
    Delay_mode_path_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_DELAY_MODE_PATH();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Delay_mode_path_directiveContext* delay_mode_path_directive();

  class  Delay_mode_unit_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Delay_mode_unit_directiveContext, antlr4::ParserRuleContext)
  public:
    Delay_mode_unit_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_DELAY_MODE_UNIT();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Delay_mode_unit_directiveContext* delay_mode_unit_directive();

  class  Delay_mode_zero_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Delay_mode_zero_directiveContext, antlr4::ParserRuleContext)
  public:
    Delay_mode_zero_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_DELAY_MODE_ZERO();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Delay_mode_zero_directiveContext* delay_mode_zero_directive();

  class  Undefineall_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Undefineall_directiveContext, antlr4::ParserRuleContext)
  public:
    Undefineall_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_UNDEFINEALL();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Undefineall_directiveContext* undefineall_directive();

  class  ModuleContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(ModuleContext, antlr4::ParserRuleContext)
  public:
    ModuleContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *MODULE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  ModuleContext* module();

  class  EndmoduleContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(EndmoduleContext, antlr4::ParserRuleContext)
  public:
    EndmoduleContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ENDMODULE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  EndmoduleContext* endmodule();

  class  Sv_interfaceContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Sv_interfaceContext, antlr4::ParserRuleContext)
  public:
    Sv_interfaceContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *INTERFACE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Sv_interfaceContext* sv_interface();

  class  EndinterfaceContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(EndinterfaceContext, antlr4::ParserRuleContext)
  public:
    EndinterfaceContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ENDINTERFACE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  EndinterfaceContext* endinterface();

  class  ProgramContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(ProgramContext, antlr4::ParserRuleContext)
  public:
    ProgramContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PROGRAM();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  ProgramContext* program();

  class  EndprogramContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(EndprogramContext, antlr4::ParserRuleContext)
  public:
    EndprogramContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ENDPROGRAM();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  EndprogramContext* endprogram();

  class  PrimitiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(PrimitiveContext, antlr4::ParserRuleContext)
  public:
    PrimitiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PRIMITIVE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  PrimitiveContext* primitive();

  class  EndprimitiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(EndprimitiveContext, antlr4::ParserRuleContext)
  public:
    EndprimitiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ENDPRIMITIVE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  EndprimitiveContext* endprimitive();

  class  Sv_packageContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Sv_packageContext, antlr4::ParserRuleContext)
  public:
    Sv_packageContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PACKAGE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Sv_packageContext* sv_package();

  class  EndpackageContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(EndpackageContext, antlr4::ParserRuleContext)
  public:
    EndpackageContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ENDPACKAGE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  EndpackageContext* endpackage();

  class  CheckerContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(CheckerContext, antlr4::ParserRuleContext)
  public:
    CheckerContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CHECKER();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  CheckerContext* checker();

  class  EndcheckerContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(EndcheckerContext, antlr4::ParserRuleContext)
  public:
    EndcheckerContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ENDCHECKER();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  EndcheckerContext* endchecker();

  class  ConfigContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(ConfigContext, antlr4::ParserRuleContext)
  public:
    ConfigContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CONFIG();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  ConfigContext* config();

  class  EndconfigContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(EndconfigContext, antlr4::ParserRuleContext)
  public:
    EndconfigContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ENDCONFIG();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  EndconfigContext* endconfig();

  class  Define_directiveContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Define_directiveContext, antlr4::ParserRuleContext)
  public:
    Define_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_DEFINE();
    std::vector<antlr4::tree::TerminalNode *> Spaces();
    antlr4::tree::TerminalNode* Spaces(size_t i);
    antlr4::tree::TerminalNode *CR();
    antlr4::tree::TerminalNode *Simple_identifier();
    antlr4::tree::TerminalNode *Escaped_identifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Define_directiveContext* define_directive();

  class  Multiline_no_args_macro_definitionContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Multiline_no_args_macro_definitionContext, antlr4::ParserRuleContext)
  public:
    Multiline_no_args_macro_definitionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_DEFINE();
    std::vector<antlr4::tree::TerminalNode *> Spaces();
    antlr4::tree::TerminalNode* Spaces(size_t i);
    Escaped_macro_definition_bodyContext *escaped_macro_definition_body();
    antlr4::tree::TerminalNode *Simple_identifier();
    antlr4::tree::TerminalNode *Escaped_identifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Multiline_no_args_macro_definitionContext* multiline_no_args_macro_definition();

  class  Multiline_args_macro_definitionContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Multiline_args_macro_definitionContext, antlr4::ParserRuleContext)
  public:
    Multiline_args_macro_definitionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_DEFINE();
    std::vector<antlr4::tree::TerminalNode *> Spaces();
    antlr4::tree::TerminalNode* Spaces(size_t i);
    Macro_argumentsContext *macro_arguments();
    Escaped_macro_definition_bodyContext *escaped_macro_definition_body();
    antlr4::tree::TerminalNode *Simple_identifier();
    antlr4::tree::TerminalNode *Escaped_identifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Multiline_args_macro_definitionContext* multiline_args_macro_definition();

  class  Simple_no_args_macro_definitionContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Simple_no_args_macro_definitionContext, antlr4::ParserRuleContext)
  public:
    Simple_no_args_macro_definitionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_DEFINE();
    std::vector<antlr4::tree::TerminalNode *> Spaces();
    antlr4::tree::TerminalNode* Spaces(size_t i);
    Simple_macro_definition_bodyContext *simple_macro_definition_body();
    antlr4::tree::TerminalNode *Simple_identifier();
    antlr4::tree::TerminalNode *Escaped_identifier();
    antlr4::tree::TerminalNode *CR();
    antlr4::tree::TerminalNode *One_line_comment();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Simple_no_args_macro_definitionContext* simple_no_args_macro_definition();

  class  Simple_args_macro_definitionContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Simple_args_macro_definitionContext, antlr4::ParserRuleContext)
  public:
    Simple_args_macro_definitionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_DEFINE();
    std::vector<antlr4::tree::TerminalNode *> Spaces();
    antlr4::tree::TerminalNode* Spaces(size_t i);
    Macro_argumentsContext *macro_arguments();
    Simple_macro_definition_bodyContext *simple_macro_definition_body();
    antlr4::tree::TerminalNode *Simple_identifier();
    antlr4::tree::TerminalNode *Escaped_identifier();
    antlr4::tree::TerminalNode *CR();
    antlr4::tree::TerminalNode *One_line_comment();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Simple_args_macro_definitionContext* simple_args_macro_definition();

  class  Identifier_in_macro_bodyContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Identifier_in_macro_bodyContext, antlr4::ParserRuleContext)
  public:
    Identifier_in_macro_bodyContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> Simple_identifier();
    antlr4::tree::TerminalNode* Simple_identifier(size_t i);
    std::vector<antlr4::tree::TerminalNode *> TICK_TICK();
    antlr4::tree::TerminalNode* TICK_TICK(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Identifier_in_macro_bodyContext* identifier_in_macro_body();

  class  Simple_no_args_macro_definition_in_macro_bodyContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Simple_no_args_macro_definition_in_macro_bodyContext, antlr4::ParserRuleContext)
  public:
    Simple_no_args_macro_definition_in_macro_bodyContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_DEFINE();
    std::vector<antlr4::tree::TerminalNode *> Spaces();
    antlr4::tree::TerminalNode* Spaces(size_t i);
    Simple_macro_definition_body_in_macro_bodyContext *simple_macro_definition_body_in_macro_body();
    Identifier_in_macro_bodyContext *identifier_in_macro_body();
    antlr4::tree::TerminalNode *Escaped_identifier();
    antlr4::tree::TerminalNode *TICK_VARIABLE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Simple_no_args_macro_definition_in_macro_bodyContext* simple_no_args_macro_definition_in_macro_body();

  class  Simple_args_macro_definition_in_macro_bodyContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Simple_args_macro_definition_in_macro_bodyContext, antlr4::ParserRuleContext)
  public:
    Simple_args_macro_definition_in_macro_bodyContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_DEFINE();
    std::vector<antlr4::tree::TerminalNode *> Spaces();
    antlr4::tree::TerminalNode* Spaces(size_t i);
    Macro_argumentsContext *macro_arguments();
    Simple_macro_definition_body_in_macro_bodyContext *simple_macro_definition_body_in_macro_body();
    Identifier_in_macro_bodyContext *identifier_in_macro_body();
    antlr4::tree::TerminalNode *Escaped_identifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Simple_args_macro_definition_in_macro_bodyContext* simple_args_macro_definition_in_macro_body();

  class  Directive_in_macroContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Directive_in_macroContext, antlr4::ParserRuleContext)
  public:
    Directive_in_macroContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Celldefine_directiveContext *celldefine_directive();
    Endcelldefine_directiveContext *endcelldefine_directive();
    Default_nettype_directiveContext *default_nettype_directive();
    Undef_directiveContext *undef_directive();
    Ifdef_directiveContext *ifdef_directive();
    Ifndef_directiveContext *ifndef_directive();
    Else_directiveContext *else_directive();
    Elsif_directiveContext *elsif_directive();
    Elseif_directiveContext *elseif_directive();
    Endif_directiveContext *endif_directive();
    Include_directiveContext *include_directive();
    Resetall_directiveContext *resetall_directive();
    Timescale_directiveContext *timescale_directive();
    Unconnected_drive_directiveContext *unconnected_drive_directive();
    Nounconnected_drive_directiveContext *nounconnected_drive_directive();
    Line_directiveContext *line_directive();
    Default_decay_time_directiveContext *default_decay_time_directive();
    Default_trireg_strenght_directiveContext *default_trireg_strenght_directive();
    Delay_mode_distributed_directiveContext *delay_mode_distributed_directive();
    Delay_mode_path_directiveContext *delay_mode_path_directive();
    Delay_mode_unit_directiveContext *delay_mode_unit_directive();
    Delay_mode_zero_directiveContext *delay_mode_zero_directive();
    Protect_directiveContext *protect_directive();
    Endprotect_directiveContext *endprotect_directive();
    Protected_directiveContext *protected_directive();
    Endprotected_directiveContext *endprotected_directive();
    Expand_vectornets_directiveContext *expand_vectornets_directive();
    Noexpand_vectornets_directiveContext *noexpand_vectornets_directive();
    Autoexpand_vectornets_directiveContext *autoexpand_vectornets_directive();
    Remove_gatename_directiveContext *remove_gatename_directive();
    Noremove_gatenames_directiveContext *noremove_gatenames_directive();
    Remove_netname_directiveContext *remove_netname_directive();
    Noremove_netnames_directiveContext *noremove_netnames_directive();
    Accelerate_directiveContext *accelerate_directive();
    Noaccelerate_directiveContext *noaccelerate_directive();
    Undefineall_directiveContext *undefineall_directive();
    Uselib_directiveContext *uselib_directive();
    Disable_portfaults_directiveContext *disable_portfaults_directive();
    Enable_portfaults_directiveContext *enable_portfaults_directive();
    Nosuppress_faults_directiveContext *nosuppress_faults_directive();
    Suppress_faults_directiveContext *suppress_faults_directive();
    Signed_directiveContext *signed_directive();
    Unsigned_directiveContext *unsigned_directive();
    Sv_file_directiveContext *sv_file_directive();
    Sv_line_directiveContext *sv_line_directive();
    Sv_packageContext *sv_package();
    EndpackageContext *endpackage();
    ModuleContext *module();
    EndmoduleContext *endmodule();
    Sv_interfaceContext *sv_interface();
    EndinterfaceContext *endinterface();
    ProgramContext *program();
    EndprogramContext *endprogram();
    PrimitiveContext *primitive();
    EndprimitiveContext *endprimitive();
    CheckerContext *checker();
    EndcheckerContext *endchecker();
    ConfigContext *config();
    EndconfigContext *endconfig();
    Simple_args_macro_definition_in_macro_bodyContext *simple_args_macro_definition_in_macro_body();
    Simple_no_args_macro_definition_in_macro_bodyContext *simple_no_args_macro_definition_in_macro_body();
    Pound_delayContext *pound_delay();
    Pound_pound_delayContext *pound_pound_delay();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Directive_in_macroContext* directive_in_macro();

  class  Macro_argumentsContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Macro_argumentsContext, antlr4::ParserRuleContext)
  public:
    Macro_argumentsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PARENS_OPEN();
    antlr4::tree::TerminalNode *PARENS_CLOSE();
    std::vector<antlr4::tree::TerminalNode *> Simple_identifier();
    antlr4::tree::TerminalNode* Simple_identifier(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Spaces();
    antlr4::tree::TerminalNode* Spaces(size_t i);
    std::vector<antlr4::tree::TerminalNode *> EQUAL_OP();
    antlr4::tree::TerminalNode* EQUAL_OP(size_t i);
    std::vector<Default_valueContext *> default_value();
    Default_valueContext* default_value(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Macro_argumentsContext* macro_arguments();

  class  Escaped_macro_definition_bodyContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Escaped_macro_definition_bodyContext, antlr4::ParserRuleContext)
  public:
    Escaped_macro_definition_bodyContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Escaped_macro_definition_body_alt1Context *escaped_macro_definition_body_alt1();
    Escaped_macro_definition_body_alt2Context *escaped_macro_definition_body_alt2();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Escaped_macro_definition_bodyContext* escaped_macro_definition_body();

  class  Escaped_macro_definition_body_alt1Context : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Escaped_macro_definition_body_alt1Context, antlr4::ParserRuleContext)
  public:
    Escaped_macro_definition_body_alt1Context(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> ESCAPED_CR();
    antlr4::tree::TerminalNode* ESCAPED_CR(size_t i);
    antlr4::tree::TerminalNode *CR();
    antlr4::tree::TerminalNode *EOF();
    std::vector<Unterminated_stringContext *> unterminated_string();
    Unterminated_stringContext* unterminated_string(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Macro_identifier();
    antlr4::tree::TerminalNode* Macro_identifier(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Macro_Escaped_identifier();
    antlr4::tree::TerminalNode* Macro_Escaped_identifier(size_t i);
    std::vector<Escaped_identifierContext *> escaped_identifier();
    Escaped_identifierContext* escaped_identifier(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Simple_identifier();
    antlr4::tree::TerminalNode* Simple_identifier(size_t i);
    std::vector<NumberContext *> number();
    NumberContext* number(size_t i);
    std::vector<antlr4::tree::TerminalNode *> TEXT_CR();
    antlr4::tree::TerminalNode* TEXT_CR(size_t i);
    std::vector<Pound_delayContext *> pound_delay();
    Pound_delayContext* pound_delay(size_t i);
    std::vector<Pound_pound_delayContext *> pound_pound_delay();
    Pound_pound_delayContext* pound_pound_delay(size_t i);
    std::vector<antlr4::tree::TerminalNode *> PARENS_OPEN();
    antlr4::tree::TerminalNode* PARENS_OPEN(size_t i);
    std::vector<antlr4::tree::TerminalNode *> PARENS_CLOSE();
    antlr4::tree::TerminalNode* PARENS_CLOSE(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    std::vector<antlr4::tree::TerminalNode *> EQUAL_OP();
    antlr4::tree::TerminalNode* EQUAL_OP(size_t i);
    std::vector<antlr4::tree::TerminalNode *> DOUBLE_QUOTE();
    antlr4::tree::TerminalNode* DOUBLE_QUOTE(size_t i);
    std::vector<antlr4::tree::TerminalNode *> TICK_VARIABLE();
    antlr4::tree::TerminalNode* TICK_VARIABLE(size_t i);
    std::vector<Directive_in_macroContext *> directive_in_macro();
    Directive_in_macroContext* directive_in_macro(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Spaces();
    antlr4::tree::TerminalNode* Spaces(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Fixed_point_number();
    antlr4::tree::TerminalNode* Fixed_point_number(size_t i);
    std::vector<antlr4::tree::TerminalNode *> String();
    antlr4::tree::TerminalNode* String(size_t i);
    std::vector<CommentsContext *> comments();
    CommentsContext* comments(size_t i);
    std::vector<antlr4::tree::TerminalNode *> TICK_QUOTE();
    antlr4::tree::TerminalNode* TICK_QUOTE(size_t i);
    std::vector<antlr4::tree::TerminalNode *> TICK_BACKSLASH_TICK_QUOTE();
    antlr4::tree::TerminalNode* TICK_BACKSLASH_TICK_QUOTE(size_t i);
    std::vector<antlr4::tree::TerminalNode *> TICK_TICK();
    antlr4::tree::TerminalNode* TICK_TICK(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Special();
    antlr4::tree::TerminalNode* Special(size_t i);
    std::vector<antlr4::tree::TerminalNode *> CURLY_OPEN();
    antlr4::tree::TerminalNode* CURLY_OPEN(size_t i);
    std::vector<antlr4::tree::TerminalNode *> CURLY_CLOSE();
    antlr4::tree::TerminalNode* CURLY_CLOSE(size_t i);
    std::vector<antlr4::tree::TerminalNode *> SQUARE_OPEN();
    antlr4::tree::TerminalNode* SQUARE_OPEN(size_t i);
    std::vector<antlr4::tree::TerminalNode *> SQUARE_CLOSE();
    antlr4::tree::TerminalNode* SQUARE_CLOSE(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Escaped_macro_definition_body_alt1Context* escaped_macro_definition_body_alt1();

  class  Escaped_macro_definition_body_alt2Context : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Escaped_macro_definition_body_alt2Context, antlr4::ParserRuleContext)
  public:
    Escaped_macro_definition_body_alt2Context(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CR();
    antlr4::tree::TerminalNode *EOF();
    std::vector<Unterminated_stringContext *> unterminated_string();
    Unterminated_stringContext* unterminated_string(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Macro_identifier();
    antlr4::tree::TerminalNode* Macro_identifier(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Macro_Escaped_identifier();
    antlr4::tree::TerminalNode* Macro_Escaped_identifier(size_t i);
    std::vector<Escaped_identifierContext *> escaped_identifier();
    Escaped_identifierContext* escaped_identifier(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Simple_identifier();
    antlr4::tree::TerminalNode* Simple_identifier(size_t i);
    std::vector<NumberContext *> number();
    NumberContext* number(size_t i);
    std::vector<antlr4::tree::TerminalNode *> TEXT_CR();
    antlr4::tree::TerminalNode* TEXT_CR(size_t i);
    std::vector<Pound_delayContext *> pound_delay();
    Pound_delayContext* pound_delay(size_t i);
    std::vector<Pound_pound_delayContext *> pound_pound_delay();
    Pound_pound_delayContext* pound_pound_delay(size_t i);
    std::vector<antlr4::tree::TerminalNode *> ESCAPED_CR();
    antlr4::tree::TerminalNode* ESCAPED_CR(size_t i);
    std::vector<antlr4::tree::TerminalNode *> PARENS_OPEN();
    antlr4::tree::TerminalNode* PARENS_OPEN(size_t i);
    std::vector<antlr4::tree::TerminalNode *> PARENS_CLOSE();
    antlr4::tree::TerminalNode* PARENS_CLOSE(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    std::vector<antlr4::tree::TerminalNode *> EQUAL_OP();
    antlr4::tree::TerminalNode* EQUAL_OP(size_t i);
    std::vector<antlr4::tree::TerminalNode *> DOUBLE_QUOTE();
    antlr4::tree::TerminalNode* DOUBLE_QUOTE(size_t i);
    std::vector<antlr4::tree::TerminalNode *> TICK_VARIABLE();
    antlr4::tree::TerminalNode* TICK_VARIABLE(size_t i);
    std::vector<Directive_in_macroContext *> directive_in_macro();
    Directive_in_macroContext* directive_in_macro(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Spaces();
    antlr4::tree::TerminalNode* Spaces(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Fixed_point_number();
    antlr4::tree::TerminalNode* Fixed_point_number(size_t i);
    std::vector<antlr4::tree::TerminalNode *> String();
    antlr4::tree::TerminalNode* String(size_t i);
    std::vector<CommentsContext *> comments();
    CommentsContext* comments(size_t i);
    std::vector<antlr4::tree::TerminalNode *> TICK_QUOTE();
    antlr4::tree::TerminalNode* TICK_QUOTE(size_t i);
    std::vector<antlr4::tree::TerminalNode *> TICK_BACKSLASH_TICK_QUOTE();
    antlr4::tree::TerminalNode* TICK_BACKSLASH_TICK_QUOTE(size_t i);
    std::vector<antlr4::tree::TerminalNode *> TICK_TICK();
    antlr4::tree::TerminalNode* TICK_TICK(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Special();
    antlr4::tree::TerminalNode* Special(size_t i);
    std::vector<antlr4::tree::TerminalNode *> CURLY_OPEN();
    antlr4::tree::TerminalNode* CURLY_OPEN(size_t i);
    std::vector<antlr4::tree::TerminalNode *> CURLY_CLOSE();
    antlr4::tree::TerminalNode* CURLY_CLOSE(size_t i);
    std::vector<antlr4::tree::TerminalNode *> SQUARE_OPEN();
    antlr4::tree::TerminalNode* SQUARE_OPEN(size_t i);
    std::vector<antlr4::tree::TerminalNode *> SQUARE_CLOSE();
    antlr4::tree::TerminalNode* SQUARE_CLOSE(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Escaped_macro_definition_body_alt2Context* escaped_macro_definition_body_alt2();

  class  Simple_macro_definition_bodyContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Simple_macro_definition_bodyContext, antlr4::ParserRuleContext)
  public:
    Simple_macro_definition_bodyContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Unterminated_stringContext *> unterminated_string();
    Unterminated_stringContext* unterminated_string(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Macro_identifier();
    antlr4::tree::TerminalNode* Macro_identifier(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Macro_Escaped_identifier();
    antlr4::tree::TerminalNode* Macro_Escaped_identifier(size_t i);
    std::vector<Escaped_identifierContext *> escaped_identifier();
    Escaped_identifierContext* escaped_identifier(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Simple_identifier();
    antlr4::tree::TerminalNode* Simple_identifier(size_t i);
    std::vector<NumberContext *> number();
    NumberContext* number(size_t i);
    std::vector<Pound_delayContext *> pound_delay();
    Pound_delayContext* pound_delay(size_t i);
    std::vector<Pound_pound_delayContext *> pound_pound_delay();
    Pound_pound_delayContext* pound_pound_delay(size_t i);
    std::vector<antlr4::tree::TerminalNode *> TEXT_CR();
    antlr4::tree::TerminalNode* TEXT_CR(size_t i);
    std::vector<antlr4::tree::TerminalNode *> PARENS_OPEN();
    antlr4::tree::TerminalNode* PARENS_OPEN(size_t i);
    std::vector<antlr4::tree::TerminalNode *> PARENS_CLOSE();
    antlr4::tree::TerminalNode* PARENS_CLOSE(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    std::vector<antlr4::tree::TerminalNode *> EQUAL_OP();
    antlr4::tree::TerminalNode* EQUAL_OP(size_t i);
    std::vector<antlr4::tree::TerminalNode *> DOUBLE_QUOTE();
    antlr4::tree::TerminalNode* DOUBLE_QUOTE(size_t i);
    std::vector<antlr4::tree::TerminalNode *> TICK_VARIABLE();
    antlr4::tree::TerminalNode* TICK_VARIABLE(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Spaces();
    antlr4::tree::TerminalNode* Spaces(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Fixed_point_number();
    antlr4::tree::TerminalNode* Fixed_point_number(size_t i);
    std::vector<antlr4::tree::TerminalNode *> String();
    antlr4::tree::TerminalNode* String(size_t i);
    std::vector<CommentsContext *> comments();
    CommentsContext* comments(size_t i);
    std::vector<antlr4::tree::TerminalNode *> TICK_QUOTE();
    antlr4::tree::TerminalNode* TICK_QUOTE(size_t i);
    std::vector<antlr4::tree::TerminalNode *> TICK_BACKSLASH_TICK_QUOTE();
    antlr4::tree::TerminalNode* TICK_BACKSLASH_TICK_QUOTE(size_t i);
    std::vector<antlr4::tree::TerminalNode *> TICK_TICK();
    antlr4::tree::TerminalNode* TICK_TICK(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Special();
    antlr4::tree::TerminalNode* Special(size_t i);
    std::vector<antlr4::tree::TerminalNode *> CURLY_OPEN();
    antlr4::tree::TerminalNode* CURLY_OPEN(size_t i);
    std::vector<antlr4::tree::TerminalNode *> CURLY_CLOSE();
    antlr4::tree::TerminalNode* CURLY_CLOSE(size_t i);
    std::vector<antlr4::tree::TerminalNode *> SQUARE_OPEN();
    antlr4::tree::TerminalNode* SQUARE_OPEN(size_t i);
    std::vector<antlr4::tree::TerminalNode *> SQUARE_CLOSE();
    antlr4::tree::TerminalNode* SQUARE_CLOSE(size_t i);
    std::vector<antlr4::tree::TerminalNode *> TICK_INCLUDE();
    antlr4::tree::TerminalNode* TICK_INCLUDE(size_t i);
    std::vector<Directive_in_macroContext *> directive_in_macro();
    Directive_in_macroContext* directive_in_macro(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Simple_macro_definition_bodyContext* simple_macro_definition_body();

  class  Simple_macro_definition_body_in_macro_bodyContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Simple_macro_definition_body_in_macro_bodyContext, antlr4::ParserRuleContext)
  public:
    Simple_macro_definition_body_in_macro_bodyContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Unterminated_stringContext *> unterminated_string();
    Unterminated_stringContext* unterminated_string(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Macro_identifier();
    antlr4::tree::TerminalNode* Macro_identifier(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Macro_Escaped_identifier();
    antlr4::tree::TerminalNode* Macro_Escaped_identifier(size_t i);
    std::vector<Escaped_identifierContext *> escaped_identifier();
    Escaped_identifierContext* escaped_identifier(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Simple_identifier();
    antlr4::tree::TerminalNode* Simple_identifier(size_t i);
    std::vector<NumberContext *> number();
    NumberContext* number(size_t i);
    std::vector<Pound_delayContext *> pound_delay();
    Pound_delayContext* pound_delay(size_t i);
    std::vector<Pound_pound_delayContext *> pound_pound_delay();
    Pound_pound_delayContext* pound_pound_delay(size_t i);
    std::vector<antlr4::tree::TerminalNode *> TEXT_CR();
    antlr4::tree::TerminalNode* TEXT_CR(size_t i);
    std::vector<antlr4::tree::TerminalNode *> PARENS_OPEN();
    antlr4::tree::TerminalNode* PARENS_OPEN(size_t i);
    std::vector<antlr4::tree::TerminalNode *> PARENS_CLOSE();
    antlr4::tree::TerminalNode* PARENS_CLOSE(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    std::vector<antlr4::tree::TerminalNode *> EQUAL_OP();
    antlr4::tree::TerminalNode* EQUAL_OP(size_t i);
    std::vector<antlr4::tree::TerminalNode *> DOUBLE_QUOTE();
    antlr4::tree::TerminalNode* DOUBLE_QUOTE(size_t i);
    std::vector<antlr4::tree::TerminalNode *> TICK_VARIABLE();
    antlr4::tree::TerminalNode* TICK_VARIABLE(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Spaces();
    antlr4::tree::TerminalNode* Spaces(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Fixed_point_number();
    antlr4::tree::TerminalNode* Fixed_point_number(size_t i);
    std::vector<antlr4::tree::TerminalNode *> String();
    antlr4::tree::TerminalNode* String(size_t i);
    std::vector<CommentsContext *> comments();
    CommentsContext* comments(size_t i);
    std::vector<antlr4::tree::TerminalNode *> TICK_QUOTE();
    antlr4::tree::TerminalNode* TICK_QUOTE(size_t i);
    std::vector<antlr4::tree::TerminalNode *> TICK_BACKSLASH_TICK_QUOTE();
    antlr4::tree::TerminalNode* TICK_BACKSLASH_TICK_QUOTE(size_t i);
    std::vector<antlr4::tree::TerminalNode *> TICK_TICK();
    antlr4::tree::TerminalNode* TICK_TICK(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Special();
    antlr4::tree::TerminalNode* Special(size_t i);
    std::vector<antlr4::tree::TerminalNode *> CURLY_OPEN();
    antlr4::tree::TerminalNode* CURLY_OPEN(size_t i);
    std::vector<antlr4::tree::TerminalNode *> CURLY_CLOSE();
    antlr4::tree::TerminalNode* CURLY_CLOSE(size_t i);
    std::vector<antlr4::tree::TerminalNode *> SQUARE_OPEN();
    antlr4::tree::TerminalNode* SQUARE_OPEN(size_t i);
    std::vector<antlr4::tree::TerminalNode *> SQUARE_CLOSE();
    antlr4::tree::TerminalNode* SQUARE_CLOSE(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Simple_macro_definition_body_in_macro_bodyContext* simple_macro_definition_body_in_macro_body();

  class  Pragma_expressionContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Pragma_expressionContext, antlr4::ParserRuleContext)
  public:
    Pragma_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Simple_identifier();
    NumberContext *number();
    antlr4::tree::TerminalNode *Spaces();
    antlr4::tree::TerminalNode *Fixed_point_number();
    antlr4::tree::TerminalNode *String();
    antlr4::tree::TerminalNode *CURLY_OPEN();
    antlr4::tree::TerminalNode *CURLY_CLOSE();
    antlr4::tree::TerminalNode *SQUARE_OPEN();
    antlr4::tree::TerminalNode *SQUARE_CLOSE();
    antlr4::tree::TerminalNode *PARENS_OPEN();
    antlr4::tree::TerminalNode *PARENS_CLOSE();
    antlr4::tree::TerminalNode *COMMA();
    antlr4::tree::TerminalNode *EQUAL_OP();
    antlr4::tree::TerminalNode *DOUBLE_QUOTE();
    Escaped_identifierContext *escaped_identifier();
    Pound_delayContext *pound_delay();
    Pound_pound_delayContext *pound_pound_delay();
    antlr4::tree::TerminalNode *Special();
    antlr4::tree::TerminalNode *ANY();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Pragma_expressionContext* pragma_expression();

  class  Macro_argContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Macro_argContext, antlr4::ParserRuleContext)
  public:
    Macro_argContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Simple_identifier();
    NumberContext *number();
    antlr4::tree::TerminalNode *Spaces();
    antlr4::tree::TerminalNode *Fixed_point_number();
    antlr4::tree::TerminalNode *String();
    Paired_parensContext *paired_parens();
    antlr4::tree::TerminalNode *EQUAL_OP();
    antlr4::tree::TerminalNode *DOUBLE_QUOTE();
    Macro_instanceContext *macro_instance();
    antlr4::tree::TerminalNode *CR();
    antlr4::tree::TerminalNode *TEXT_CR();
    Escaped_identifierContext *escaped_identifier();
    Simple_args_macro_definition_in_macro_bodyContext *simple_args_macro_definition_in_macro_body();
    Simple_no_args_macro_definition_in_macro_bodyContext *simple_no_args_macro_definition_in_macro_body();
    CommentsContext *comments();
    Pound_delayContext *pound_delay();
    Pound_pound_delayContext *pound_pound_delay();
    antlr4::tree::TerminalNode *Special();
    antlr4::tree::TerminalNode *ANY();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Macro_argContext* macro_arg();

  class  Paired_parensContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Paired_parensContext, antlr4::ParserRuleContext)
  public:
    Paired_parensContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PARENS_OPEN();
    antlr4::tree::TerminalNode *PARENS_CLOSE();
    std::vector<antlr4::tree::TerminalNode *> Simple_identifier();
    antlr4::tree::TerminalNode* Simple_identifier(size_t i);
    std::vector<NumberContext *> number();
    NumberContext* number(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Spaces();
    antlr4::tree::TerminalNode* Spaces(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Fixed_point_number();
    antlr4::tree::TerminalNode* Fixed_point_number(size_t i);
    std::vector<antlr4::tree::TerminalNode *> String();
    antlr4::tree::TerminalNode* String(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    std::vector<antlr4::tree::TerminalNode *> EQUAL_OP();
    antlr4::tree::TerminalNode* EQUAL_OP(size_t i);
    std::vector<antlr4::tree::TerminalNode *> DOUBLE_QUOTE();
    antlr4::tree::TerminalNode* DOUBLE_QUOTE(size_t i);
    std::vector<Macro_instanceContext *> macro_instance();
    Macro_instanceContext* macro_instance(size_t i);
    std::vector<antlr4::tree::TerminalNode *> TEXT_CR();
    antlr4::tree::TerminalNode* TEXT_CR(size_t i);
    std::vector<antlr4::tree::TerminalNode *> CR();
    antlr4::tree::TerminalNode* CR(size_t i);
    std::vector<Paired_parensContext *> paired_parens();
    Paired_parensContext* paired_parens(size_t i);
    std::vector<Escaped_identifierContext *> escaped_identifier();
    Escaped_identifierContext* escaped_identifier(size_t i);
    std::vector<CommentsContext *> comments();
    CommentsContext* comments(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Special();
    antlr4::tree::TerminalNode* Special(size_t i);
    std::vector<antlr4::tree::TerminalNode *> ANY();
    antlr4::tree::TerminalNode* ANY(size_t i);
    antlr4::tree::TerminalNode *CURLY_OPEN();
    antlr4::tree::TerminalNode *CURLY_CLOSE();
    antlr4::tree::TerminalNode *SQUARE_OPEN();
    antlr4::tree::TerminalNode *SQUARE_CLOSE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Paired_parensContext* paired_parens();

  class  Text_blobContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Text_blobContext, antlr4::ParserRuleContext)
  public:
    Text_blobContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Simple_identifier();
    NumberContext *number();
    antlr4::tree::TerminalNode *CR();
    antlr4::tree::TerminalNode *Spaces();
    antlr4::tree::TerminalNode *Fixed_point_number();
    antlr4::tree::TerminalNode *ESCAPED_CR();
    antlr4::tree::TerminalNode *String();
    antlr4::tree::TerminalNode *PARENS_OPEN();
    antlr4::tree::TerminalNode *PARENS_CLOSE();
    antlr4::tree::TerminalNode *COMMA();
    antlr4::tree::TerminalNode *EQUAL_OP();
    antlr4::tree::TerminalNode *DOUBLE_QUOTE();
    antlr4::tree::TerminalNode *CURLY_OPEN();
    antlr4::tree::TerminalNode *CURLY_CLOSE();
    antlr4::tree::TerminalNode *SQUARE_OPEN();
    antlr4::tree::TerminalNode *SQUARE_CLOSE();
    antlr4::tree::TerminalNode *TICK_TICK();
    antlr4::tree::TerminalNode *TICK_VARIABLE();
    antlr4::tree::TerminalNode *TIMESCALE();
    Pound_delayContext *pound_delay();
    Pound_pound_delayContext *pound_pound_delay();
    antlr4::tree::TerminalNode *TICK_QUOTE();
    antlr4::tree::TerminalNode *TICK_BACKSLASH_TICK_QUOTE();
    antlr4::tree::TerminalNode *TEXT_CR();
    antlr4::tree::TerminalNode *Special();
    antlr4::tree::TerminalNode *ANY();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Text_blobContext* text_blob();

  class  StringContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(StringContext, antlr4::ParserRuleContext)
  public:
    StringContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *String();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  StringContext* string();

  class  Default_valueContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(Default_valueContext, antlr4::ParserRuleContext)
  public:
    Default_valueContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Simple_identifier();
    NumberContext *number();
    antlr4::tree::TerminalNode *Spaces();
    antlr4::tree::TerminalNode *Fixed_point_number();
    antlr4::tree::TerminalNode *String();
    antlr4::tree::TerminalNode *CURLY_OPEN();
    antlr4::tree::TerminalNode *CURLY_CLOSE();
    antlr4::tree::TerminalNode *SQUARE_OPEN();
    antlr4::tree::TerminalNode *SQUARE_CLOSE();
    Paired_parensContext *paired_parens();
    Escaped_identifierContext *escaped_identifier();
    Macro_instanceContext *macro_instance();
    antlr4::tree::TerminalNode *Special();
    antlr4::tree::TerminalNode *ANY();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Default_valueContext* default_value();

  class  String_blobContext : public antlr4::ParserRuleContext {
    IMPLEMENT_RTTI(String_blobContext, antlr4::ParserRuleContext)
  public:
    String_blobContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Simple_identifier();
    NumberContext *number();
    antlr4::tree::TerminalNode *Spaces();
    antlr4::tree::TerminalNode *Fixed_point_number();
    antlr4::tree::TerminalNode *ESCAPED_CR();
    antlr4::tree::TerminalNode *PARENS_OPEN();
    antlr4::tree::TerminalNode *PARENS_CLOSE();
    antlr4::tree::TerminalNode *COMMA();
    antlr4::tree::TerminalNode *EQUAL_OP();
    antlr4::tree::TerminalNode *DOUBLE_QUOTE();
    antlr4::tree::TerminalNode *CURLY_OPEN();
    antlr4::tree::TerminalNode *CURLY_CLOSE();
    antlr4::tree::TerminalNode *SQUARE_OPEN();
    antlr4::tree::TerminalNode *SQUARE_CLOSE();
    Escaped_identifierContext *escaped_identifier();
    antlr4::tree::TerminalNode *TIMESCALE();
    Pound_delayContext *pound_delay();
    Pound_pound_delayContext *pound_pound_delay();
    antlr4::tree::TerminalNode *TEXT_CR();
    antlr4::tree::TerminalNode *Special();
    antlr4::tree::TerminalNode *ANY();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  String_blobContext* string_blob();


private:
  static std::vector<antlr4::dfa::DFA> _decisionToDFA;
  static antlr4::atn::PredictionContextCache _sharedContextCache;
  static std::vector<std::string> _ruleNames;
  static std::vector<std::string> _tokenNames;

  static std::vector<std::string> _literalNames;
  static std::vector<std::string> _symbolicNames;
  static antlr4::dfa::Vocabulary _vocabulary;
  static antlr4::atn::ATN _atn;
  static std::vector<uint16_t> _serializedATN;


  struct Initializer {
    Initializer();
  };
  static Initializer _init;
};

