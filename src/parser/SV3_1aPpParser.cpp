
// Generated from SV3_1aPpParser.g4 by ANTLR 4.9.1


#include "SV3_1aPpParserListener.h"

#include "SV3_1aPpParser.h"


using namespace antlrcpp;
using namespace antlr4;

SV3_1aPpParser::SV3_1aPpParser(TokenStream *input) : Parser(input) {
  _interpreter = new atn::ParserATNSimulator(this, _atn, _decisionToDFA, _sharedContextCache);
}

SV3_1aPpParser::~SV3_1aPpParser() {
  delete _interpreter;
}

std::string SV3_1aPpParser::getGrammarFileName() const {
  return "SV3_1aPpParser.g4";
}

const std::vector<std::string>& SV3_1aPpParser::getRuleNames() const {
  return _ruleNames;
}

dfa::Vocabulary& SV3_1aPpParser::getVocabulary() const {
  return _vocabulary;
}


//----------------- Top_level_ruleContext ------------------------------------------------------------------

SV3_1aPpParser::Top_level_ruleContext::Top_level_ruleContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

SV3_1aPpParser::Null_ruleContext* SV3_1aPpParser::Top_level_ruleContext::null_rule() {
  return getRuleContext<SV3_1aPpParser::Null_ruleContext>(0);
}

SV3_1aPpParser::Source_textContext* SV3_1aPpParser::Top_level_ruleContext::source_text() {
  return getRuleContext<SV3_1aPpParser::Source_textContext>(0);
}

tree::TerminalNode* SV3_1aPpParser::Top_level_ruleContext::EOF() {
  return getToken(SV3_1aPpParser::EOF, 0);
}


size_t SV3_1aPpParser::Top_level_ruleContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleTop_level_rule;
}

void SV3_1aPpParser::Top_level_ruleContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterTop_level_rule(this);
}

void SV3_1aPpParser::Top_level_ruleContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitTop_level_rule(this);
}

SV3_1aPpParser::Top_level_ruleContext* SV3_1aPpParser::top_level_rule() {
  Top_level_ruleContext *_localctx = _tracker.createInstance<Top_level_ruleContext>(_ctx, getState());
  enterRule(_localctx, 0, SV3_1aPpParser::RuleTop_level_rule);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(202);
    null_rule();
    setState(203);
    source_text();
    setState(204);
    match(SV3_1aPpParser::EOF);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Source_textContext ------------------------------------------------------------------

SV3_1aPpParser::Source_textContext::Source_textContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<SV3_1aPpParser::DescriptionContext *> SV3_1aPpParser::Source_textContext::description() {
  return getRuleContexts<SV3_1aPpParser::DescriptionContext>();
}

SV3_1aPpParser::DescriptionContext* SV3_1aPpParser::Source_textContext::description(size_t i) {
  return getRuleContext<SV3_1aPpParser::DescriptionContext>(i);
}


size_t SV3_1aPpParser::Source_textContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleSource_text;
}

void SV3_1aPpParser::Source_textContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterSource_text(this);
}

void SV3_1aPpParser::Source_textContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitSource_text(this);
}

SV3_1aPpParser::Source_textContext* SV3_1aPpParser::source_text() {
  Source_textContext *_localctx = _tracker.createInstance<Source_textContext>(_ctx, getState());
  enterRule(_localctx, 2, SV3_1aPpParser::RuleSource_text);
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(209);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while ((((_la & ~ 0x3fULL) == 0) &&
      ((1ULL << _la) & ((1ULL << SV3_1aPpParser::One_line_comment)
      | (1ULL << SV3_1aPpParser::Block_comment)
      | (1ULL << SV3_1aPpParser::TICK_VARIABLE)
      | (1ULL << SV3_1aPpParser::TICK_DEFINE)
      | (1ULL << SV3_1aPpParser::TICK_CELLDEFINE)
      | (1ULL << SV3_1aPpParser::TICK_ENDCELLDEFINE)
      | (1ULL << SV3_1aPpParser::TICK_DEFAULT_NETTYPE)
      | (1ULL << SV3_1aPpParser::TICK_UNDEF)
      | (1ULL << SV3_1aPpParser::TICK_IFDEF)
      | (1ULL << SV3_1aPpParser::TICK_IFNDEF)
      | (1ULL << SV3_1aPpParser::TICK_ELSE)
      | (1ULL << SV3_1aPpParser::TICK_ELSIF)
      | (1ULL << SV3_1aPpParser::TICK_ELSEIF)
      | (1ULL << SV3_1aPpParser::TICK_ENDIF)
      | (1ULL << SV3_1aPpParser::TICK_INCLUDE)
      | (1ULL << SV3_1aPpParser::TICK_PRAGMA)
      | (1ULL << SV3_1aPpParser::TICK_BEGIN_KEYWORDS)
      | (1ULL << SV3_1aPpParser::TICK_END_KEYWORDS)
      | (1ULL << SV3_1aPpParser::TICK_RESETALL)
      | (1ULL << SV3_1aPpParser::TICK_TIMESCALE)
      | (1ULL << SV3_1aPpParser::TICK_UNCONNECTED_DRIVE)
      | (1ULL << SV3_1aPpParser::TICK_NOUNCONNECTED_DRIVE)
      | (1ULL << SV3_1aPpParser::TICK_LINE)
      | (1ULL << SV3_1aPpParser::TICK_DEFAULT_DECAY_TIME)
      | (1ULL << SV3_1aPpParser::TICK_DEFAULT_TRIREG_STRENGTH)
      | (1ULL << SV3_1aPpParser::TICK_DELAY_MODE_DISTRIBUTED)
      | (1ULL << SV3_1aPpParser::TICK_DELAY_MODE_PATH)
      | (1ULL << SV3_1aPpParser::TICK_DELAY_MODE_UNIT)
      | (1ULL << SV3_1aPpParser::TICK_DELAY_MODE_ZERO)
      | (1ULL << SV3_1aPpParser::TICK_UNDEFINEALL)
      | (1ULL << SV3_1aPpParser::TICK_ACCELERATE)
      | (1ULL << SV3_1aPpParser::TICK_NOACCELERATE)
      | (1ULL << SV3_1aPpParser::TICK_PROTECT)
      | (1ULL << SV3_1aPpParser::TICK_USELIB)
      | (1ULL << SV3_1aPpParser::TICK_DISABLE_PORTFAULTS)
      | (1ULL << SV3_1aPpParser::TICK_ENABLE_PORTFAULTS)
      | (1ULL << SV3_1aPpParser::TICK_NOSUPPRESS_FAULTS)
      | (1ULL << SV3_1aPpParser::TICK_SUPPRESS_FAULTS)
      | (1ULL << SV3_1aPpParser::TICK_SIGNED)
      | (1ULL << SV3_1aPpParser::TICK_UNSIGNED)
      | (1ULL << SV3_1aPpParser::TICK_ENDPROTECT)
      | (1ULL << SV3_1aPpParser::TICK_PROTECTED)
      | (1ULL << SV3_1aPpParser::TICK_ENDPROTECTED)
      | (1ULL << SV3_1aPpParser::TICK_EXPAND_VECTORNETS)
      | (1ULL << SV3_1aPpParser::TICK_NOEXPAND_VECTORNETS)
      | (1ULL << SV3_1aPpParser::TICK_AUTOEXPAND_VECTORNETS)
      | (1ULL << SV3_1aPpParser::TICK_REMOVE_GATENAME)
      | (1ULL << SV3_1aPpParser::TICK_NOREMOVE_GATENAMES)
      | (1ULL << SV3_1aPpParser::TICK_REMOVE_NETNAME)
      | (1ULL << SV3_1aPpParser::TICK_NOREMOVE_NETNAMES)
      | (1ULL << SV3_1aPpParser::TICK_FILE__)
      | (1ULL << SV3_1aPpParser::TICK_LINE__)
      | (1ULL << SV3_1aPpParser::MODULE)
      | (1ULL << SV3_1aPpParser::ENDMODULE)
      | (1ULL << SV3_1aPpParser::INTERFACE)
      | (1ULL << SV3_1aPpParser::ENDINTERFACE)
      | (1ULL << SV3_1aPpParser::PROGRAM)
      | (1ULL << SV3_1aPpParser::ENDPROGRAM)
      | (1ULL << SV3_1aPpParser::PRIMITIVE)
      | (1ULL << SV3_1aPpParser::ENDPRIMITIVE)
      | (1ULL << SV3_1aPpParser::PACKAGE)
      | (1ULL << SV3_1aPpParser::ENDPACKAGE)
      | (1ULL << SV3_1aPpParser::CHECKER))) != 0) || ((((_la - 64) & ~ 0x3fULL) == 0) &&
      ((1ULL << (_la - 64)) & ((1ULL << (SV3_1aPpParser::ENDCHECKER - 64))
      | (1ULL << (SV3_1aPpParser::CONFIG - 64))
      | (1ULL << (SV3_1aPpParser::ENDCONFIG - 64))
      | (1ULL << (SV3_1aPpParser::Macro_identifier - 64))
      | (1ULL << (SV3_1aPpParser::Macro_Escaped_identifier - 64))
      | (1ULL << (SV3_1aPpParser::String - 64))
      | (1ULL << (SV3_1aPpParser::Simple_identifier - 64))
      | (1ULL << (SV3_1aPpParser::Spaces - 64))
      | (1ULL << (SV3_1aPpParser::Pound_Pound_delay - 64))
      | (1ULL << (SV3_1aPpParser::Pound_delay - 64))
      | (1ULL << (SV3_1aPpParser::TIMESCALE - 64))
      | (1ULL << (SV3_1aPpParser::Number - 64))
      | (1ULL << (SV3_1aPpParser::Fixed_point_number - 64))
      | (1ULL << (SV3_1aPpParser::TEXT_CR - 64))
      | (1ULL << (SV3_1aPpParser::ESCAPED_CR - 64))
      | (1ULL << (SV3_1aPpParser::CR - 64))
      | (1ULL << (SV3_1aPpParser::TICK_QUOTE - 64))
      | (1ULL << (SV3_1aPpParser::TICK_BACKSLASH_TICK_QUOTE - 64))
      | (1ULL << (SV3_1aPpParser::TICK_TICK - 64))
      | (1ULL << (SV3_1aPpParser::PARENS_OPEN - 64))
      | (1ULL << (SV3_1aPpParser::PARENS_CLOSE - 64))
      | (1ULL << (SV3_1aPpParser::COMMA - 64))
      | (1ULL << (SV3_1aPpParser::EQUAL_OP - 64))
      | (1ULL << (SV3_1aPpParser::DOUBLE_QUOTE - 64))
      | (1ULL << (SV3_1aPpParser::Escaped_identifier - 64))
      | (1ULL << (SV3_1aPpParser::CURLY_OPEN - 64))
      | (1ULL << (SV3_1aPpParser::CURLY_CLOSE - 64))
      | (1ULL << (SV3_1aPpParser::SQUARE_OPEN - 64))
      | (1ULL << (SV3_1aPpParser::SQUARE_CLOSE - 64))
      | (1ULL << (SV3_1aPpParser::Special - 64))
      | (1ULL << (SV3_1aPpParser::ANY - 64)))) != 0)) {
      setState(206);
      description();
      setState(211);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Null_ruleContext ------------------------------------------------------------------

SV3_1aPpParser::Null_ruleContext::Null_ruleContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}


size_t SV3_1aPpParser::Null_ruleContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleNull_rule;
}

void SV3_1aPpParser::Null_ruleContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterNull_rule(this);
}

void SV3_1aPpParser::Null_ruleContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitNull_rule(this);
}

SV3_1aPpParser::Null_ruleContext* SV3_1aPpParser::null_rule() {
  Null_ruleContext *_localctx = _tracker.createInstance<Null_ruleContext>(_ctx, getState());
  enterRule(_localctx, 4, SV3_1aPpParser::RuleNull_rule);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);

   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- DescriptionContext ------------------------------------------------------------------

SV3_1aPpParser::DescriptionContext::DescriptionContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

SV3_1aPpParser::Unterminated_stringContext* SV3_1aPpParser::DescriptionContext::unterminated_string() {
  return getRuleContext<SV3_1aPpParser::Unterminated_stringContext>(0);
}

SV3_1aPpParser::StringContext* SV3_1aPpParser::DescriptionContext::string() {
  return getRuleContext<SV3_1aPpParser::StringContext>(0);
}

SV3_1aPpParser::NumberContext* SV3_1aPpParser::DescriptionContext::number() {
  return getRuleContext<SV3_1aPpParser::NumberContext>(0);
}

SV3_1aPpParser::Macro_definitionContext* SV3_1aPpParser::DescriptionContext::macro_definition() {
  return getRuleContext<SV3_1aPpParser::Macro_definitionContext>(0);
}

SV3_1aPpParser::CommentsContext* SV3_1aPpParser::DescriptionContext::comments() {
  return getRuleContext<SV3_1aPpParser::CommentsContext>(0);
}

SV3_1aPpParser::Celldefine_directiveContext* SV3_1aPpParser::DescriptionContext::celldefine_directive() {
  return getRuleContext<SV3_1aPpParser::Celldefine_directiveContext>(0);
}

SV3_1aPpParser::Endcelldefine_directiveContext* SV3_1aPpParser::DescriptionContext::endcelldefine_directive() {
  return getRuleContext<SV3_1aPpParser::Endcelldefine_directiveContext>(0);
}

SV3_1aPpParser::Default_nettype_directiveContext* SV3_1aPpParser::DescriptionContext::default_nettype_directive() {
  return getRuleContext<SV3_1aPpParser::Default_nettype_directiveContext>(0);
}

SV3_1aPpParser::Undef_directiveContext* SV3_1aPpParser::DescriptionContext::undef_directive() {
  return getRuleContext<SV3_1aPpParser::Undef_directiveContext>(0);
}

SV3_1aPpParser::Ifdef_directiveContext* SV3_1aPpParser::DescriptionContext::ifdef_directive() {
  return getRuleContext<SV3_1aPpParser::Ifdef_directiveContext>(0);
}

SV3_1aPpParser::Ifndef_directiveContext* SV3_1aPpParser::DescriptionContext::ifndef_directive() {
  return getRuleContext<SV3_1aPpParser::Ifndef_directiveContext>(0);
}

SV3_1aPpParser::Else_directiveContext* SV3_1aPpParser::DescriptionContext::else_directive() {
  return getRuleContext<SV3_1aPpParser::Else_directiveContext>(0);
}

SV3_1aPpParser::Elsif_directiveContext* SV3_1aPpParser::DescriptionContext::elsif_directive() {
  return getRuleContext<SV3_1aPpParser::Elsif_directiveContext>(0);
}

SV3_1aPpParser::Elseif_directiveContext* SV3_1aPpParser::DescriptionContext::elseif_directive() {
  return getRuleContext<SV3_1aPpParser::Elseif_directiveContext>(0);
}

SV3_1aPpParser::Endif_directiveContext* SV3_1aPpParser::DescriptionContext::endif_directive() {
  return getRuleContext<SV3_1aPpParser::Endif_directiveContext>(0);
}

SV3_1aPpParser::Include_directiveContext* SV3_1aPpParser::DescriptionContext::include_directive() {
  return getRuleContext<SV3_1aPpParser::Include_directiveContext>(0);
}

SV3_1aPpParser::Resetall_directiveContext* SV3_1aPpParser::DescriptionContext::resetall_directive() {
  return getRuleContext<SV3_1aPpParser::Resetall_directiveContext>(0);
}

SV3_1aPpParser::Begin_keywords_directiveContext* SV3_1aPpParser::DescriptionContext::begin_keywords_directive() {
  return getRuleContext<SV3_1aPpParser::Begin_keywords_directiveContext>(0);
}

SV3_1aPpParser::End_keywords_directiveContext* SV3_1aPpParser::DescriptionContext::end_keywords_directive() {
  return getRuleContext<SV3_1aPpParser::End_keywords_directiveContext>(0);
}

SV3_1aPpParser::Timescale_directiveContext* SV3_1aPpParser::DescriptionContext::timescale_directive() {
  return getRuleContext<SV3_1aPpParser::Timescale_directiveContext>(0);
}

SV3_1aPpParser::Unconnected_drive_directiveContext* SV3_1aPpParser::DescriptionContext::unconnected_drive_directive() {
  return getRuleContext<SV3_1aPpParser::Unconnected_drive_directiveContext>(0);
}

SV3_1aPpParser::Nounconnected_drive_directiveContext* SV3_1aPpParser::DescriptionContext::nounconnected_drive_directive() {
  return getRuleContext<SV3_1aPpParser::Nounconnected_drive_directiveContext>(0);
}

SV3_1aPpParser::Line_directiveContext* SV3_1aPpParser::DescriptionContext::line_directive() {
  return getRuleContext<SV3_1aPpParser::Line_directiveContext>(0);
}

SV3_1aPpParser::Default_decay_time_directiveContext* SV3_1aPpParser::DescriptionContext::default_decay_time_directive() {
  return getRuleContext<SV3_1aPpParser::Default_decay_time_directiveContext>(0);
}

SV3_1aPpParser::Default_trireg_strenght_directiveContext* SV3_1aPpParser::DescriptionContext::default_trireg_strenght_directive() {
  return getRuleContext<SV3_1aPpParser::Default_trireg_strenght_directiveContext>(0);
}

SV3_1aPpParser::Delay_mode_distributed_directiveContext* SV3_1aPpParser::DescriptionContext::delay_mode_distributed_directive() {
  return getRuleContext<SV3_1aPpParser::Delay_mode_distributed_directiveContext>(0);
}

SV3_1aPpParser::Delay_mode_path_directiveContext* SV3_1aPpParser::DescriptionContext::delay_mode_path_directive() {
  return getRuleContext<SV3_1aPpParser::Delay_mode_path_directiveContext>(0);
}

SV3_1aPpParser::Delay_mode_unit_directiveContext* SV3_1aPpParser::DescriptionContext::delay_mode_unit_directive() {
  return getRuleContext<SV3_1aPpParser::Delay_mode_unit_directiveContext>(0);
}

SV3_1aPpParser::Delay_mode_zero_directiveContext* SV3_1aPpParser::DescriptionContext::delay_mode_zero_directive() {
  return getRuleContext<SV3_1aPpParser::Delay_mode_zero_directiveContext>(0);
}

SV3_1aPpParser::Protect_directiveContext* SV3_1aPpParser::DescriptionContext::protect_directive() {
  return getRuleContext<SV3_1aPpParser::Protect_directiveContext>(0);
}

SV3_1aPpParser::Endprotect_directiveContext* SV3_1aPpParser::DescriptionContext::endprotect_directive() {
  return getRuleContext<SV3_1aPpParser::Endprotect_directiveContext>(0);
}

SV3_1aPpParser::Protected_directiveContext* SV3_1aPpParser::DescriptionContext::protected_directive() {
  return getRuleContext<SV3_1aPpParser::Protected_directiveContext>(0);
}

SV3_1aPpParser::Endprotected_directiveContext* SV3_1aPpParser::DescriptionContext::endprotected_directive() {
  return getRuleContext<SV3_1aPpParser::Endprotected_directiveContext>(0);
}

SV3_1aPpParser::Expand_vectornets_directiveContext* SV3_1aPpParser::DescriptionContext::expand_vectornets_directive() {
  return getRuleContext<SV3_1aPpParser::Expand_vectornets_directiveContext>(0);
}

SV3_1aPpParser::Noexpand_vectornets_directiveContext* SV3_1aPpParser::DescriptionContext::noexpand_vectornets_directive() {
  return getRuleContext<SV3_1aPpParser::Noexpand_vectornets_directiveContext>(0);
}

SV3_1aPpParser::Autoexpand_vectornets_directiveContext* SV3_1aPpParser::DescriptionContext::autoexpand_vectornets_directive() {
  return getRuleContext<SV3_1aPpParser::Autoexpand_vectornets_directiveContext>(0);
}

SV3_1aPpParser::Remove_gatename_directiveContext* SV3_1aPpParser::DescriptionContext::remove_gatename_directive() {
  return getRuleContext<SV3_1aPpParser::Remove_gatename_directiveContext>(0);
}

SV3_1aPpParser::Noremove_gatenames_directiveContext* SV3_1aPpParser::DescriptionContext::noremove_gatenames_directive() {
  return getRuleContext<SV3_1aPpParser::Noremove_gatenames_directiveContext>(0);
}

SV3_1aPpParser::Remove_netname_directiveContext* SV3_1aPpParser::DescriptionContext::remove_netname_directive() {
  return getRuleContext<SV3_1aPpParser::Remove_netname_directiveContext>(0);
}

SV3_1aPpParser::Noremove_netnames_directiveContext* SV3_1aPpParser::DescriptionContext::noremove_netnames_directive() {
  return getRuleContext<SV3_1aPpParser::Noremove_netnames_directiveContext>(0);
}

SV3_1aPpParser::Accelerate_directiveContext* SV3_1aPpParser::DescriptionContext::accelerate_directive() {
  return getRuleContext<SV3_1aPpParser::Accelerate_directiveContext>(0);
}

SV3_1aPpParser::Noaccelerate_directiveContext* SV3_1aPpParser::DescriptionContext::noaccelerate_directive() {
  return getRuleContext<SV3_1aPpParser::Noaccelerate_directiveContext>(0);
}

SV3_1aPpParser::Undefineall_directiveContext* SV3_1aPpParser::DescriptionContext::undefineall_directive() {
  return getRuleContext<SV3_1aPpParser::Undefineall_directiveContext>(0);
}

SV3_1aPpParser::Uselib_directiveContext* SV3_1aPpParser::DescriptionContext::uselib_directive() {
  return getRuleContext<SV3_1aPpParser::Uselib_directiveContext>(0);
}

SV3_1aPpParser::Disable_portfaults_directiveContext* SV3_1aPpParser::DescriptionContext::disable_portfaults_directive() {
  return getRuleContext<SV3_1aPpParser::Disable_portfaults_directiveContext>(0);
}

SV3_1aPpParser::Enable_portfaults_directiveContext* SV3_1aPpParser::DescriptionContext::enable_portfaults_directive() {
  return getRuleContext<SV3_1aPpParser::Enable_portfaults_directiveContext>(0);
}

SV3_1aPpParser::Nosuppress_faults_directiveContext* SV3_1aPpParser::DescriptionContext::nosuppress_faults_directive() {
  return getRuleContext<SV3_1aPpParser::Nosuppress_faults_directiveContext>(0);
}

SV3_1aPpParser::Suppress_faults_directiveContext* SV3_1aPpParser::DescriptionContext::suppress_faults_directive() {
  return getRuleContext<SV3_1aPpParser::Suppress_faults_directiveContext>(0);
}

SV3_1aPpParser::Signed_directiveContext* SV3_1aPpParser::DescriptionContext::signed_directive() {
  return getRuleContext<SV3_1aPpParser::Signed_directiveContext>(0);
}

SV3_1aPpParser::Unsigned_directiveContext* SV3_1aPpParser::DescriptionContext::unsigned_directive() {
  return getRuleContext<SV3_1aPpParser::Unsigned_directiveContext>(0);
}

SV3_1aPpParser::Pragma_directiveContext* SV3_1aPpParser::DescriptionContext::pragma_directive() {
  return getRuleContext<SV3_1aPpParser::Pragma_directiveContext>(0);
}

SV3_1aPpParser::Sv_file_directiveContext* SV3_1aPpParser::DescriptionContext::sv_file_directive() {
  return getRuleContext<SV3_1aPpParser::Sv_file_directiveContext>(0);
}

SV3_1aPpParser::Sv_line_directiveContext* SV3_1aPpParser::DescriptionContext::sv_line_directive() {
  return getRuleContext<SV3_1aPpParser::Sv_line_directiveContext>(0);
}

SV3_1aPpParser::Macro_instanceContext* SV3_1aPpParser::DescriptionContext::macro_instance() {
  return getRuleContext<SV3_1aPpParser::Macro_instanceContext>(0);
}

SV3_1aPpParser::ModuleContext* SV3_1aPpParser::DescriptionContext::module() {
  return getRuleContext<SV3_1aPpParser::ModuleContext>(0);
}

SV3_1aPpParser::EndmoduleContext* SV3_1aPpParser::DescriptionContext::endmodule() {
  return getRuleContext<SV3_1aPpParser::EndmoduleContext>(0);
}

SV3_1aPpParser::Sv_interfaceContext* SV3_1aPpParser::DescriptionContext::sv_interface() {
  return getRuleContext<SV3_1aPpParser::Sv_interfaceContext>(0);
}

SV3_1aPpParser::EndinterfaceContext* SV3_1aPpParser::DescriptionContext::endinterface() {
  return getRuleContext<SV3_1aPpParser::EndinterfaceContext>(0);
}

SV3_1aPpParser::ProgramContext* SV3_1aPpParser::DescriptionContext::program() {
  return getRuleContext<SV3_1aPpParser::ProgramContext>(0);
}

SV3_1aPpParser::EndprogramContext* SV3_1aPpParser::DescriptionContext::endprogram() {
  return getRuleContext<SV3_1aPpParser::EndprogramContext>(0);
}

SV3_1aPpParser::PrimitiveContext* SV3_1aPpParser::DescriptionContext::primitive() {
  return getRuleContext<SV3_1aPpParser::PrimitiveContext>(0);
}

SV3_1aPpParser::EndprimitiveContext* SV3_1aPpParser::DescriptionContext::endprimitive() {
  return getRuleContext<SV3_1aPpParser::EndprimitiveContext>(0);
}

SV3_1aPpParser::Sv_packageContext* SV3_1aPpParser::DescriptionContext::sv_package() {
  return getRuleContext<SV3_1aPpParser::Sv_packageContext>(0);
}

SV3_1aPpParser::EndpackageContext* SV3_1aPpParser::DescriptionContext::endpackage() {
  return getRuleContext<SV3_1aPpParser::EndpackageContext>(0);
}

SV3_1aPpParser::CheckerContext* SV3_1aPpParser::DescriptionContext::checker() {
  return getRuleContext<SV3_1aPpParser::CheckerContext>(0);
}

SV3_1aPpParser::EndcheckerContext* SV3_1aPpParser::DescriptionContext::endchecker() {
  return getRuleContext<SV3_1aPpParser::EndcheckerContext>(0);
}

SV3_1aPpParser::ConfigContext* SV3_1aPpParser::DescriptionContext::config() {
  return getRuleContext<SV3_1aPpParser::ConfigContext>(0);
}

SV3_1aPpParser::EndconfigContext* SV3_1aPpParser::DescriptionContext::endconfig() {
  return getRuleContext<SV3_1aPpParser::EndconfigContext>(0);
}

SV3_1aPpParser::Text_blobContext* SV3_1aPpParser::DescriptionContext::text_blob() {
  return getRuleContext<SV3_1aPpParser::Text_blobContext>(0);
}

SV3_1aPpParser::Escaped_identifierContext* SV3_1aPpParser::DescriptionContext::escaped_identifier() {
  return getRuleContext<SV3_1aPpParser::Escaped_identifierContext>(0);
}

SV3_1aPpParser::Pound_delayContext* SV3_1aPpParser::DescriptionContext::pound_delay() {
  return getRuleContext<SV3_1aPpParser::Pound_delayContext>(0);
}

SV3_1aPpParser::Pound_pound_delayContext* SV3_1aPpParser::DescriptionContext::pound_pound_delay() {
  return getRuleContext<SV3_1aPpParser::Pound_pound_delayContext>(0);
}


size_t SV3_1aPpParser::DescriptionContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleDescription;
}

void SV3_1aPpParser::DescriptionContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterDescription(this);
}

void SV3_1aPpParser::DescriptionContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitDescription(this);
}

SV3_1aPpParser::DescriptionContext* SV3_1aPpParser::description() {
  DescriptionContext *_localctx = _tracker.createInstance<DescriptionContext>(_ctx, getState());
  enterRule(_localctx, 6, SV3_1aPpParser::RuleDescription);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    setState(286);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 1, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(214);
      unterminated_string();
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(215);
      string();
      break;
    }

    case 3: {
      enterOuterAlt(_localctx, 3);
      setState(216);
      number();
      break;
    }

    case 4: {
      enterOuterAlt(_localctx, 4);
      setState(217);
      macro_definition();
      break;
    }

    case 5: {
      enterOuterAlt(_localctx, 5);
      setState(218);
      comments();
      break;
    }

    case 6: {
      enterOuterAlt(_localctx, 6);
      setState(219);
      celldefine_directive();
      break;
    }

    case 7: {
      enterOuterAlt(_localctx, 7);
      setState(220);
      endcelldefine_directive();
      break;
    }

    case 8: {
      enterOuterAlt(_localctx, 8);
      setState(221);
      default_nettype_directive();
      break;
    }

    case 9: {
      enterOuterAlt(_localctx, 9);
      setState(222);
      undef_directive();
      break;
    }

    case 10: {
      enterOuterAlt(_localctx, 10);
      setState(223);
      ifdef_directive();
      break;
    }

    case 11: {
      enterOuterAlt(_localctx, 11);
      setState(224);
      ifndef_directive();
      break;
    }

    case 12: {
      enterOuterAlt(_localctx, 12);
      setState(225);
      else_directive();
      break;
    }

    case 13: {
      enterOuterAlt(_localctx, 13);
      setState(226);
      elsif_directive();
      break;
    }

    case 14: {
      enterOuterAlt(_localctx, 14);
      setState(227);
      elseif_directive();
      break;
    }

    case 15: {
      enterOuterAlt(_localctx, 15);
      setState(228);
      endif_directive();
      break;
    }

    case 16: {
      enterOuterAlt(_localctx, 16);
      setState(229);
      include_directive();
      break;
    }

    case 17: {
      enterOuterAlt(_localctx, 17);
      setState(230);
      resetall_directive();
      break;
    }

    case 18: {
      enterOuterAlt(_localctx, 18);
      setState(231);
      begin_keywords_directive();
      break;
    }

    case 19: {
      enterOuterAlt(_localctx, 19);
      setState(232);
      end_keywords_directive();
      break;
    }

    case 20: {
      enterOuterAlt(_localctx, 20);
      setState(233);
      timescale_directive();
      break;
    }

    case 21: {
      enterOuterAlt(_localctx, 21);
      setState(234);
      unconnected_drive_directive();
      break;
    }

    case 22: {
      enterOuterAlt(_localctx, 22);
      setState(235);
      nounconnected_drive_directive();
      break;
    }

    case 23: {
      enterOuterAlt(_localctx, 23);
      setState(236);
      line_directive();
      break;
    }

    case 24: {
      enterOuterAlt(_localctx, 24);
      setState(237);
      default_decay_time_directive();
      break;
    }

    case 25: {
      enterOuterAlt(_localctx, 25);
      setState(238);
      default_trireg_strenght_directive();
      break;
    }

    case 26: {
      enterOuterAlt(_localctx, 26);
      setState(239);
      delay_mode_distributed_directive();
      break;
    }

    case 27: {
      enterOuterAlt(_localctx, 27);
      setState(240);
      delay_mode_path_directive();
      break;
    }

    case 28: {
      enterOuterAlt(_localctx, 28);
      setState(241);
      delay_mode_unit_directive();
      break;
    }

    case 29: {
      enterOuterAlt(_localctx, 29);
      setState(242);
      delay_mode_zero_directive();
      break;
    }

    case 30: {
      enterOuterAlt(_localctx, 30);
      setState(243);
      protect_directive();
      break;
    }

    case 31: {
      enterOuterAlt(_localctx, 31);
      setState(244);
      endprotect_directive();
      break;
    }

    case 32: {
      enterOuterAlt(_localctx, 32);
      setState(245);
      protected_directive();
      break;
    }

    case 33: {
      enterOuterAlt(_localctx, 33);
      setState(246);
      endprotected_directive();
      break;
    }

    case 34: {
      enterOuterAlt(_localctx, 34);
      setState(247);
      expand_vectornets_directive();
      break;
    }

    case 35: {
      enterOuterAlt(_localctx, 35);
      setState(248);
      noexpand_vectornets_directive();
      break;
    }

    case 36: {
      enterOuterAlt(_localctx, 36);
      setState(249);
      autoexpand_vectornets_directive();
      break;
    }

    case 37: {
      enterOuterAlt(_localctx, 37);
      setState(250);
      remove_gatename_directive();
      break;
    }

    case 38: {
      enterOuterAlt(_localctx, 38);
      setState(251);
      noremove_gatenames_directive();
      break;
    }

    case 39: {
      enterOuterAlt(_localctx, 39);
      setState(252);
      remove_netname_directive();
      break;
    }

    case 40: {
      enterOuterAlt(_localctx, 40);
      setState(253);
      noremove_netnames_directive();
      break;
    }

    case 41: {
      enterOuterAlt(_localctx, 41);
      setState(254);
      accelerate_directive();
      break;
    }

    case 42: {
      enterOuterAlt(_localctx, 42);
      setState(255);
      noaccelerate_directive();
      break;
    }

    case 43: {
      enterOuterAlt(_localctx, 43);
      setState(256);
      undefineall_directive();
      break;
    }

    case 44: {
      enterOuterAlt(_localctx, 44);
      setState(257);
      uselib_directive();
      break;
    }

    case 45: {
      enterOuterAlt(_localctx, 45);
      setState(258);
      disable_portfaults_directive();
      break;
    }

    case 46: {
      enterOuterAlt(_localctx, 46);
      setState(259);
      enable_portfaults_directive();
      break;
    }

    case 47: {
      enterOuterAlt(_localctx, 47);
      setState(260);
      nosuppress_faults_directive();
      break;
    }

    case 48: {
      enterOuterAlt(_localctx, 48);
      setState(261);
      suppress_faults_directive();
      break;
    }

    case 49: {
      enterOuterAlt(_localctx, 49);
      setState(262);
      signed_directive();
      break;
    }

    case 50: {
      enterOuterAlt(_localctx, 50);
      setState(263);
      unsigned_directive();
      break;
    }

    case 51: {
      enterOuterAlt(_localctx, 51);
      setState(264);
      pragma_directive();
      break;
    }

    case 52: {
      enterOuterAlt(_localctx, 52);
      setState(265);
      sv_file_directive();
      break;
    }

    case 53: {
      enterOuterAlt(_localctx, 53);
      setState(266);
      sv_line_directive();
      break;
    }

    case 54: {
      enterOuterAlt(_localctx, 54);
      setState(267);
      macro_instance();
      break;
    }

    case 55: {
      enterOuterAlt(_localctx, 55);
      setState(268);
      module();
      break;
    }

    case 56: {
      enterOuterAlt(_localctx, 56);
      setState(269);
      endmodule();
      break;
    }

    case 57: {
      enterOuterAlt(_localctx, 57);
      setState(270);
      sv_interface();
      break;
    }

    case 58: {
      enterOuterAlt(_localctx, 58);
      setState(271);
      endinterface();
      break;
    }

    case 59: {
      enterOuterAlt(_localctx, 59);
      setState(272);
      program();
      break;
    }

    case 60: {
      enterOuterAlt(_localctx, 60);
      setState(273);
      endprogram();
      break;
    }

    case 61: {
      enterOuterAlt(_localctx, 61);
      setState(274);
      primitive();
      break;
    }

    case 62: {
      enterOuterAlt(_localctx, 62);
      setState(275);
      endprimitive();
      break;
    }

    case 63: {
      enterOuterAlt(_localctx, 63);
      setState(276);
      sv_package();
      break;
    }

    case 64: {
      enterOuterAlt(_localctx, 64);
      setState(277);
      endpackage();
      break;
    }

    case 65: {
      enterOuterAlt(_localctx, 65);
      setState(278);
      checker();
      break;
    }

    case 66: {
      enterOuterAlt(_localctx, 66);
      setState(279);
      endchecker();
      break;
    }

    case 67: {
      enterOuterAlt(_localctx, 67);
      setState(280);
      config();
      break;
    }

    case 68: {
      enterOuterAlt(_localctx, 68);
      setState(281);
      endconfig();
      break;
    }

    case 69: {
      enterOuterAlt(_localctx, 69);
      setState(282);
      text_blob();
      break;
    }

    case 70: {
      enterOuterAlt(_localctx, 70);
      setState(283);
      escaped_identifier();
      break;
    }

    case 71: {
      enterOuterAlt(_localctx, 71);
      setState(284);
      pound_delay();
      break;
    }

    case 72: {
      enterOuterAlt(_localctx, 72);
      setState(285);
      pound_pound_delay();
      break;
    }

    default:
      break;
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Macro_instanceContext ------------------------------------------------------------------

SV3_1aPpParser::Macro_instanceContext::Macro_instanceContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}


size_t SV3_1aPpParser::Macro_instanceContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleMacro_instance;
}

void SV3_1aPpParser::Macro_instanceContext::copyFrom(Macro_instanceContext *ctx) {
  ParserRuleContext::copyFrom(ctx);
}

//----------------- MacroInstanceWithArgsContext ------------------------------------------------------------------

tree::TerminalNode* SV3_1aPpParser::MacroInstanceWithArgsContext::PARENS_OPEN() {
  return getToken(SV3_1aPpParser::PARENS_OPEN, 0);
}

SV3_1aPpParser::Macro_actual_argsContext* SV3_1aPpParser::MacroInstanceWithArgsContext::macro_actual_args() {
  return getRuleContext<SV3_1aPpParser::Macro_actual_argsContext>(0);
}

tree::TerminalNode* SV3_1aPpParser::MacroInstanceWithArgsContext::PARENS_CLOSE() {
  return getToken(SV3_1aPpParser::PARENS_CLOSE, 0);
}

tree::TerminalNode* SV3_1aPpParser::MacroInstanceWithArgsContext::Macro_identifier() {
  return getToken(SV3_1aPpParser::Macro_identifier, 0);
}

tree::TerminalNode* SV3_1aPpParser::MacroInstanceWithArgsContext::Macro_Escaped_identifier() {
  return getToken(SV3_1aPpParser::Macro_Escaped_identifier, 0);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::MacroInstanceWithArgsContext::Spaces() {
  return getTokens(SV3_1aPpParser::Spaces);
}

tree::TerminalNode* SV3_1aPpParser::MacroInstanceWithArgsContext::Spaces(size_t i) {
  return getToken(SV3_1aPpParser::Spaces, i);
}

SV3_1aPpParser::MacroInstanceWithArgsContext::MacroInstanceWithArgsContext(Macro_instanceContext *ctx) { copyFrom(ctx); }

void SV3_1aPpParser::MacroInstanceWithArgsContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterMacroInstanceWithArgs(this);
}
void SV3_1aPpParser::MacroInstanceWithArgsContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitMacroInstanceWithArgs(this);
}
//----------------- MacroInstanceNoArgsContext ------------------------------------------------------------------

tree::TerminalNode* SV3_1aPpParser::MacroInstanceNoArgsContext::Macro_identifier() {
  return getToken(SV3_1aPpParser::Macro_identifier, 0);
}

tree::TerminalNode* SV3_1aPpParser::MacroInstanceNoArgsContext::Macro_Escaped_identifier() {
  return getToken(SV3_1aPpParser::Macro_Escaped_identifier, 0);
}

SV3_1aPpParser::MacroInstanceNoArgsContext::MacroInstanceNoArgsContext(Macro_instanceContext *ctx) { copyFrom(ctx); }

void SV3_1aPpParser::MacroInstanceNoArgsContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterMacroInstanceNoArgs(this);
}
void SV3_1aPpParser::MacroInstanceNoArgsContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitMacroInstanceNoArgs(this);
}
SV3_1aPpParser::Macro_instanceContext* SV3_1aPpParser::macro_instance() {
  Macro_instanceContext *_localctx = _tracker.createInstance<Macro_instanceContext>(_ctx, getState());
  enterRule(_localctx, 8, SV3_1aPpParser::RuleMacro_instance);
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    setState(300);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 3, _ctx)) {
    case 1: {
      _localctx = dynamic_cast<Macro_instanceContext *>(_tracker.createInstance<SV3_1aPpParser::MacroInstanceWithArgsContext>(_localctx));
      enterOuterAlt(_localctx, 1);
      setState(288);
      _la = _input->LA(1);
      if (!(_la == SV3_1aPpParser::Macro_identifier

      || _la == SV3_1aPpParser::Macro_Escaped_identifier)) {
      _errHandler->recoverInline(this);
      }
      else {
        _errHandler->reportMatch(this);
        consume();
      }
      setState(292);
      _errHandler->sync(this);
      _la = _input->LA(1);
      while (_la == SV3_1aPpParser::Spaces) {
        setState(289);
        match(SV3_1aPpParser::Spaces);
        setState(294);
        _errHandler->sync(this);
        _la = _input->LA(1);
      }
      setState(295);
      match(SV3_1aPpParser::PARENS_OPEN);
      setState(296);
      macro_actual_args();
      setState(297);
      match(SV3_1aPpParser::PARENS_CLOSE);
      break;
    }

    case 2: {
      _localctx = dynamic_cast<Macro_instanceContext *>(_tracker.createInstance<SV3_1aPpParser::MacroInstanceNoArgsContext>(_localctx));
      enterOuterAlt(_localctx, 2);
      setState(299);
      _la = _input->LA(1);
      if (!(_la == SV3_1aPpParser::Macro_identifier

      || _la == SV3_1aPpParser::Macro_Escaped_identifier)) {
      _errHandler->recoverInline(this);
      }
      else {
        _errHandler->reportMatch(this);
        consume();
      }
      break;
    }

    default:
      break;
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Unterminated_stringContext ------------------------------------------------------------------

SV3_1aPpParser::Unterminated_stringContext::Unterminated_stringContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Unterminated_stringContext::DOUBLE_QUOTE() {
  return getToken(SV3_1aPpParser::DOUBLE_QUOTE, 0);
}

tree::TerminalNode* SV3_1aPpParser::Unterminated_stringContext::CR() {
  return getToken(SV3_1aPpParser::CR, 0);
}

std::vector<SV3_1aPpParser::String_blobContext *> SV3_1aPpParser::Unterminated_stringContext::string_blob() {
  return getRuleContexts<SV3_1aPpParser::String_blobContext>();
}

SV3_1aPpParser::String_blobContext* SV3_1aPpParser::Unterminated_stringContext::string_blob(size_t i) {
  return getRuleContext<SV3_1aPpParser::String_blobContext>(i);
}


size_t SV3_1aPpParser::Unterminated_stringContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleUnterminated_string;
}

void SV3_1aPpParser::Unterminated_stringContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterUnterminated_string(this);
}

void SV3_1aPpParser::Unterminated_stringContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitUnterminated_string(this);
}

SV3_1aPpParser::Unterminated_stringContext* SV3_1aPpParser::unterminated_string() {
  Unterminated_stringContext *_localctx = _tracker.createInstance<Unterminated_stringContext>(_ctx, getState());
  enterRule(_localctx, 10, SV3_1aPpParser::RuleUnterminated_string);
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(302);
    match(SV3_1aPpParser::DOUBLE_QUOTE);
    setState(306);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (((((_la - 70) & ~ 0x3fULL) == 0) &&
      ((1ULL << (_la - 70)) & ((1ULL << (SV3_1aPpParser::Simple_identifier - 70))
      | (1ULL << (SV3_1aPpParser::Spaces - 70))
      | (1ULL << (SV3_1aPpParser::Pound_Pound_delay - 70))
      | (1ULL << (SV3_1aPpParser::Pound_delay - 70))
      | (1ULL << (SV3_1aPpParser::TIMESCALE - 70))
      | (1ULL << (SV3_1aPpParser::Number - 70))
      | (1ULL << (SV3_1aPpParser::Fixed_point_number - 70))
      | (1ULL << (SV3_1aPpParser::TEXT_CR - 70))
      | (1ULL << (SV3_1aPpParser::ESCAPED_CR - 70))
      | (1ULL << (SV3_1aPpParser::PARENS_OPEN - 70))
      | (1ULL << (SV3_1aPpParser::PARENS_CLOSE - 70))
      | (1ULL << (SV3_1aPpParser::COMMA - 70))
      | (1ULL << (SV3_1aPpParser::EQUAL_OP - 70))
      | (1ULL << (SV3_1aPpParser::DOUBLE_QUOTE - 70))
      | (1ULL << (SV3_1aPpParser::Escaped_identifier - 70))
      | (1ULL << (SV3_1aPpParser::CURLY_OPEN - 70))
      | (1ULL << (SV3_1aPpParser::CURLY_CLOSE - 70))
      | (1ULL << (SV3_1aPpParser::SQUARE_OPEN - 70))
      | (1ULL << (SV3_1aPpParser::SQUARE_CLOSE - 70))
      | (1ULL << (SV3_1aPpParser::Special - 70))
      | (1ULL << (SV3_1aPpParser::ANY - 70)))) != 0)) {
      setState(303);
      string_blob();
      setState(308);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
    setState(309);
    match(SV3_1aPpParser::CR);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Macro_actual_argsContext ------------------------------------------------------------------

SV3_1aPpParser::Macro_actual_argsContext::Macro_actual_argsContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<SV3_1aPpParser::Macro_argContext *> SV3_1aPpParser::Macro_actual_argsContext::macro_arg() {
  return getRuleContexts<SV3_1aPpParser::Macro_argContext>();
}

SV3_1aPpParser::Macro_argContext* SV3_1aPpParser::Macro_actual_argsContext::macro_arg(size_t i) {
  return getRuleContext<SV3_1aPpParser::Macro_argContext>(i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Macro_actual_argsContext::COMMA() {
  return getTokens(SV3_1aPpParser::COMMA);
}

tree::TerminalNode* SV3_1aPpParser::Macro_actual_argsContext::COMMA(size_t i) {
  return getToken(SV3_1aPpParser::COMMA, i);
}


size_t SV3_1aPpParser::Macro_actual_argsContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleMacro_actual_args;
}

void SV3_1aPpParser::Macro_actual_argsContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterMacro_actual_args(this);
}

void SV3_1aPpParser::Macro_actual_argsContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitMacro_actual_args(this);
}

SV3_1aPpParser::Macro_actual_argsContext* SV3_1aPpParser::macro_actual_args() {
  Macro_actual_argsContext *_localctx = _tracker.createInstance<Macro_actual_argsContext>(_ctx, getState());
  enterRule(_localctx, 12, SV3_1aPpParser::RuleMacro_actual_args);
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(314);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while ((((_la & ~ 0x3fULL) == 0) &&
      ((1ULL << _la) & ((1ULL << SV3_1aPpParser::One_line_comment)
      | (1ULL << SV3_1aPpParser::Block_comment)
      | (1ULL << SV3_1aPpParser::TICK_DEFINE))) != 0) || ((((_la - 67) & ~ 0x3fULL) == 0) &&
      ((1ULL << (_la - 67)) & ((1ULL << (SV3_1aPpParser::Macro_identifier - 67))
      | (1ULL << (SV3_1aPpParser::Macro_Escaped_identifier - 67))
      | (1ULL << (SV3_1aPpParser::String - 67))
      | (1ULL << (SV3_1aPpParser::Simple_identifier - 67))
      | (1ULL << (SV3_1aPpParser::Spaces - 67))
      | (1ULL << (SV3_1aPpParser::Pound_Pound_delay - 67))
      | (1ULL << (SV3_1aPpParser::Pound_delay - 67))
      | (1ULL << (SV3_1aPpParser::Number - 67))
      | (1ULL << (SV3_1aPpParser::Fixed_point_number - 67))
      | (1ULL << (SV3_1aPpParser::TEXT_CR - 67))
      | (1ULL << (SV3_1aPpParser::CR - 67))
      | (1ULL << (SV3_1aPpParser::PARENS_OPEN - 67))
      | (1ULL << (SV3_1aPpParser::EQUAL_OP - 67))
      | (1ULL << (SV3_1aPpParser::DOUBLE_QUOTE - 67))
      | (1ULL << (SV3_1aPpParser::Escaped_identifier - 67))
      | (1ULL << (SV3_1aPpParser::CURLY_OPEN - 67))
      | (1ULL << (SV3_1aPpParser::SQUARE_OPEN - 67))
      | (1ULL << (SV3_1aPpParser::Special - 67))
      | (1ULL << (SV3_1aPpParser::ANY - 67)))) != 0)) {
      setState(311);
      macro_arg();
      setState(316);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
    setState(326);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (_la == SV3_1aPpParser::COMMA) {
      setState(317);
      match(SV3_1aPpParser::COMMA);
      setState(321);
      _errHandler->sync(this);
      _la = _input->LA(1);
      while ((((_la & ~ 0x3fULL) == 0) &&
        ((1ULL << _la) & ((1ULL << SV3_1aPpParser::One_line_comment)
        | (1ULL << SV3_1aPpParser::Block_comment)
        | (1ULL << SV3_1aPpParser::TICK_DEFINE))) != 0) || ((((_la - 67) & ~ 0x3fULL) == 0) &&
        ((1ULL << (_la - 67)) & ((1ULL << (SV3_1aPpParser::Macro_identifier - 67))
        | (1ULL << (SV3_1aPpParser::Macro_Escaped_identifier - 67))
        | (1ULL << (SV3_1aPpParser::String - 67))
        | (1ULL << (SV3_1aPpParser::Simple_identifier - 67))
        | (1ULL << (SV3_1aPpParser::Spaces - 67))
        | (1ULL << (SV3_1aPpParser::Pound_Pound_delay - 67))
        | (1ULL << (SV3_1aPpParser::Pound_delay - 67))
        | (1ULL << (SV3_1aPpParser::Number - 67))
        | (1ULL << (SV3_1aPpParser::Fixed_point_number - 67))
        | (1ULL << (SV3_1aPpParser::TEXT_CR - 67))
        | (1ULL << (SV3_1aPpParser::CR - 67))
        | (1ULL << (SV3_1aPpParser::PARENS_OPEN - 67))
        | (1ULL << (SV3_1aPpParser::EQUAL_OP - 67))
        | (1ULL << (SV3_1aPpParser::DOUBLE_QUOTE - 67))
        | (1ULL << (SV3_1aPpParser::Escaped_identifier - 67))
        | (1ULL << (SV3_1aPpParser::CURLY_OPEN - 67))
        | (1ULL << (SV3_1aPpParser::SQUARE_OPEN - 67))
        | (1ULL << (SV3_1aPpParser::Special - 67))
        | (1ULL << (SV3_1aPpParser::ANY - 67)))) != 0)) {
        setState(318);
        macro_arg();
        setState(323);
        _errHandler->sync(this);
        _la = _input->LA(1);
      }
      setState(328);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- CommentsContext ------------------------------------------------------------------

SV3_1aPpParser::CommentsContext::CommentsContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::CommentsContext::One_line_comment() {
  return getToken(SV3_1aPpParser::One_line_comment, 0);
}

tree::TerminalNode* SV3_1aPpParser::CommentsContext::Block_comment() {
  return getToken(SV3_1aPpParser::Block_comment, 0);
}


size_t SV3_1aPpParser::CommentsContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleComments;
}

void SV3_1aPpParser::CommentsContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterComments(this);
}

void SV3_1aPpParser::CommentsContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitComments(this);
}

SV3_1aPpParser::CommentsContext* SV3_1aPpParser::comments() {
  CommentsContext *_localctx = _tracker.createInstance<CommentsContext>(_ctx, getState());
  enterRule(_localctx, 14, SV3_1aPpParser::RuleComments);
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(329);
    _la = _input->LA(1);
    if (!(_la == SV3_1aPpParser::One_line_comment

    || _la == SV3_1aPpParser::Block_comment)) {
    _errHandler->recoverInline(this);
    }
    else {
      _errHandler->reportMatch(this);
      consume();
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- NumberContext ------------------------------------------------------------------

SV3_1aPpParser::NumberContext::NumberContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::NumberContext::Number() {
  return getToken(SV3_1aPpParser::Number, 0);
}


size_t SV3_1aPpParser::NumberContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleNumber;
}

void SV3_1aPpParser::NumberContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterNumber(this);
}

void SV3_1aPpParser::NumberContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitNumber(this);
}

SV3_1aPpParser::NumberContext* SV3_1aPpParser::number() {
  NumberContext *_localctx = _tracker.createInstance<NumberContext>(_ctx, getState());
  enterRule(_localctx, 16, SV3_1aPpParser::RuleNumber);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(331);
    match(SV3_1aPpParser::Number);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Pound_delayContext ------------------------------------------------------------------

SV3_1aPpParser::Pound_delayContext::Pound_delayContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Pound_delayContext::Pound_delay() {
  return getToken(SV3_1aPpParser::Pound_delay, 0);
}


size_t SV3_1aPpParser::Pound_delayContext::getRuleIndex() const {
  return SV3_1aPpParser::RulePound_delay;
}

void SV3_1aPpParser::Pound_delayContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterPound_delay(this);
}

void SV3_1aPpParser::Pound_delayContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitPound_delay(this);
}

SV3_1aPpParser::Pound_delayContext* SV3_1aPpParser::pound_delay() {
  Pound_delayContext *_localctx = _tracker.createInstance<Pound_delayContext>(_ctx, getState());
  enterRule(_localctx, 18, SV3_1aPpParser::RulePound_delay);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(333);
    match(SV3_1aPpParser::Pound_delay);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Pound_pound_delayContext ------------------------------------------------------------------

SV3_1aPpParser::Pound_pound_delayContext::Pound_pound_delayContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Pound_pound_delayContext::Pound_Pound_delay() {
  return getToken(SV3_1aPpParser::Pound_Pound_delay, 0);
}


size_t SV3_1aPpParser::Pound_pound_delayContext::getRuleIndex() const {
  return SV3_1aPpParser::RulePound_pound_delay;
}

void SV3_1aPpParser::Pound_pound_delayContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterPound_pound_delay(this);
}

void SV3_1aPpParser::Pound_pound_delayContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitPound_pound_delay(this);
}

SV3_1aPpParser::Pound_pound_delayContext* SV3_1aPpParser::pound_pound_delay() {
  Pound_pound_delayContext *_localctx = _tracker.createInstance<Pound_pound_delayContext>(_ctx, getState());
  enterRule(_localctx, 20, SV3_1aPpParser::RulePound_pound_delay);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(335);
    match(SV3_1aPpParser::Pound_Pound_delay);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Macro_definitionContext ------------------------------------------------------------------

SV3_1aPpParser::Macro_definitionContext::Macro_definitionContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

SV3_1aPpParser::Define_directiveContext* SV3_1aPpParser::Macro_definitionContext::define_directive() {
  return getRuleContext<SV3_1aPpParser::Define_directiveContext>(0);
}

SV3_1aPpParser::Multiline_args_macro_definitionContext* SV3_1aPpParser::Macro_definitionContext::multiline_args_macro_definition() {
  return getRuleContext<SV3_1aPpParser::Multiline_args_macro_definitionContext>(0);
}

SV3_1aPpParser::Simple_no_args_macro_definitionContext* SV3_1aPpParser::Macro_definitionContext::simple_no_args_macro_definition() {
  return getRuleContext<SV3_1aPpParser::Simple_no_args_macro_definitionContext>(0);
}

SV3_1aPpParser::Multiline_no_args_macro_definitionContext* SV3_1aPpParser::Macro_definitionContext::multiline_no_args_macro_definition() {
  return getRuleContext<SV3_1aPpParser::Multiline_no_args_macro_definitionContext>(0);
}

SV3_1aPpParser::Simple_args_macro_definitionContext* SV3_1aPpParser::Macro_definitionContext::simple_args_macro_definition() {
  return getRuleContext<SV3_1aPpParser::Simple_args_macro_definitionContext>(0);
}


size_t SV3_1aPpParser::Macro_definitionContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleMacro_definition;
}

void SV3_1aPpParser::Macro_definitionContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterMacro_definition(this);
}

void SV3_1aPpParser::Macro_definitionContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitMacro_definition(this);
}

SV3_1aPpParser::Macro_definitionContext* SV3_1aPpParser::macro_definition() {
  Macro_definitionContext *_localctx = _tracker.createInstance<Macro_definitionContext>(_ctx, getState());
  enterRule(_localctx, 22, SV3_1aPpParser::RuleMacro_definition);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    setState(342);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 8, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(337);
      define_directive();
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(338);
      multiline_args_macro_definition();
      break;
    }

    case 3: {
      enterOuterAlt(_localctx, 3);
      setState(339);
      simple_no_args_macro_definition();
      break;
    }

    case 4: {
      enterOuterAlt(_localctx, 4);
      setState(340);
      multiline_no_args_macro_definition();
      break;
    }

    case 5: {
      enterOuterAlt(_localctx, 5);
      setState(341);
      simple_args_macro_definition();
      break;
    }

    default:
      break;
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Include_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Include_directiveContext::Include_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Include_directiveContext::TICK_INCLUDE() {
  return getToken(SV3_1aPpParser::TICK_INCLUDE, 0);
}

tree::TerminalNode* SV3_1aPpParser::Include_directiveContext::Spaces() {
  return getToken(SV3_1aPpParser::Spaces, 0);
}

tree::TerminalNode* SV3_1aPpParser::Include_directiveContext::String() {
  return getToken(SV3_1aPpParser::String, 0);
}

tree::TerminalNode* SV3_1aPpParser::Include_directiveContext::Simple_identifier() {
  return getToken(SV3_1aPpParser::Simple_identifier, 0);
}

tree::TerminalNode* SV3_1aPpParser::Include_directiveContext::Escaped_identifier() {
  return getToken(SV3_1aPpParser::Escaped_identifier, 0);
}

SV3_1aPpParser::Macro_instanceContext* SV3_1aPpParser::Include_directiveContext::macro_instance() {
  return getRuleContext<SV3_1aPpParser::Macro_instanceContext>(0);
}


size_t SV3_1aPpParser::Include_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleInclude_directive;
}

void SV3_1aPpParser::Include_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterInclude_directive(this);
}

void SV3_1aPpParser::Include_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitInclude_directive(this);
}

SV3_1aPpParser::Include_directiveContext* SV3_1aPpParser::include_directive() {
  Include_directiveContext *_localctx = _tracker.createInstance<Include_directiveContext>(_ctx, getState());
  enterRule(_localctx, 24, SV3_1aPpParser::RuleInclude_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(344);
    match(SV3_1aPpParser::TICK_INCLUDE);
    setState(345);
    match(SV3_1aPpParser::Spaces);
    setState(350);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case SV3_1aPpParser::String: {
        setState(346);
        match(SV3_1aPpParser::String);
        break;
      }

      case SV3_1aPpParser::Simple_identifier: {
        setState(347);
        match(SV3_1aPpParser::Simple_identifier);
        break;
      }

      case SV3_1aPpParser::Escaped_identifier: {
        setState(348);
        match(SV3_1aPpParser::Escaped_identifier);
        break;
      }

      case SV3_1aPpParser::Macro_identifier:
      case SV3_1aPpParser::Macro_Escaped_identifier: {
        setState(349);
        macro_instance();
        break;
      }

    default:
      throw NoViableAltException(this);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Line_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Line_directiveContext::Line_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Line_directiveContext::TICK_LINE() {
  return getToken(SV3_1aPpParser::TICK_LINE, 0);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Line_directiveContext::Spaces() {
  return getTokens(SV3_1aPpParser::Spaces);
}

tree::TerminalNode* SV3_1aPpParser::Line_directiveContext::Spaces(size_t i) {
  return getToken(SV3_1aPpParser::Spaces, i);
}

std::vector<SV3_1aPpParser::NumberContext *> SV3_1aPpParser::Line_directiveContext::number() {
  return getRuleContexts<SV3_1aPpParser::NumberContext>();
}

SV3_1aPpParser::NumberContext* SV3_1aPpParser::Line_directiveContext::number(size_t i) {
  return getRuleContext<SV3_1aPpParser::NumberContext>(i);
}

tree::TerminalNode* SV3_1aPpParser::Line_directiveContext::String() {
  return getToken(SV3_1aPpParser::String, 0);
}


size_t SV3_1aPpParser::Line_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleLine_directive;
}

void SV3_1aPpParser::Line_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterLine_directive(this);
}

void SV3_1aPpParser::Line_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitLine_directive(this);
}

SV3_1aPpParser::Line_directiveContext* SV3_1aPpParser::line_directive() {
  Line_directiveContext *_localctx = _tracker.createInstance<Line_directiveContext>(_ctx, getState());
  enterRule(_localctx, 26, SV3_1aPpParser::RuleLine_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(352);
    match(SV3_1aPpParser::TICK_LINE);
    setState(353);
    match(SV3_1aPpParser::Spaces);
    setState(354);
    number();
    setState(355);
    match(SV3_1aPpParser::String);
    setState(356);
    match(SV3_1aPpParser::Spaces);
    setState(357);
    number();
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Default_nettype_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Default_nettype_directiveContext::Default_nettype_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Default_nettype_directiveContext::TICK_DEFAULT_NETTYPE() {
  return getToken(SV3_1aPpParser::TICK_DEFAULT_NETTYPE, 0);
}

tree::TerminalNode* SV3_1aPpParser::Default_nettype_directiveContext::Spaces() {
  return getToken(SV3_1aPpParser::Spaces, 0);
}

tree::TerminalNode* SV3_1aPpParser::Default_nettype_directiveContext::Simple_identifier() {
  return getToken(SV3_1aPpParser::Simple_identifier, 0);
}


size_t SV3_1aPpParser::Default_nettype_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleDefault_nettype_directive;
}

void SV3_1aPpParser::Default_nettype_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterDefault_nettype_directive(this);
}

void SV3_1aPpParser::Default_nettype_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitDefault_nettype_directive(this);
}

SV3_1aPpParser::Default_nettype_directiveContext* SV3_1aPpParser::default_nettype_directive() {
  Default_nettype_directiveContext *_localctx = _tracker.createInstance<Default_nettype_directiveContext>(_ctx, getState());
  enterRule(_localctx, 28, SV3_1aPpParser::RuleDefault_nettype_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(359);
    match(SV3_1aPpParser::TICK_DEFAULT_NETTYPE);
    setState(360);
    match(SV3_1aPpParser::Spaces);
    setState(361);
    match(SV3_1aPpParser::Simple_identifier);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Sv_file_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Sv_file_directiveContext::Sv_file_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Sv_file_directiveContext::TICK_FILE__() {
  return getToken(SV3_1aPpParser::TICK_FILE__, 0);
}


size_t SV3_1aPpParser::Sv_file_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleSv_file_directive;
}

void SV3_1aPpParser::Sv_file_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterSv_file_directive(this);
}

void SV3_1aPpParser::Sv_file_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitSv_file_directive(this);
}

SV3_1aPpParser::Sv_file_directiveContext* SV3_1aPpParser::sv_file_directive() {
  Sv_file_directiveContext *_localctx = _tracker.createInstance<Sv_file_directiveContext>(_ctx, getState());
  enterRule(_localctx, 30, SV3_1aPpParser::RuleSv_file_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(363);
    match(SV3_1aPpParser::TICK_FILE__);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Sv_line_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Sv_line_directiveContext::Sv_line_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Sv_line_directiveContext::TICK_LINE__() {
  return getToken(SV3_1aPpParser::TICK_LINE__, 0);
}


size_t SV3_1aPpParser::Sv_line_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleSv_line_directive;
}

void SV3_1aPpParser::Sv_line_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterSv_line_directive(this);
}

void SV3_1aPpParser::Sv_line_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitSv_line_directive(this);
}

SV3_1aPpParser::Sv_line_directiveContext* SV3_1aPpParser::sv_line_directive() {
  Sv_line_directiveContext *_localctx = _tracker.createInstance<Sv_line_directiveContext>(_ctx, getState());
  enterRule(_localctx, 32, SV3_1aPpParser::RuleSv_line_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(365);
    match(SV3_1aPpParser::TICK_LINE__);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Timescale_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Timescale_directiveContext::Timescale_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Timescale_directiveContext::TICK_TIMESCALE() {
  return getToken(SV3_1aPpParser::TICK_TIMESCALE, 0);
}

tree::TerminalNode* SV3_1aPpParser::Timescale_directiveContext::TIMESCALE() {
  return getToken(SV3_1aPpParser::TIMESCALE, 0);
}


size_t SV3_1aPpParser::Timescale_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleTimescale_directive;
}

void SV3_1aPpParser::Timescale_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterTimescale_directive(this);
}

void SV3_1aPpParser::Timescale_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitTimescale_directive(this);
}

SV3_1aPpParser::Timescale_directiveContext* SV3_1aPpParser::timescale_directive() {
  Timescale_directiveContext *_localctx = _tracker.createInstance<Timescale_directiveContext>(_ctx, getState());
  enterRule(_localctx, 34, SV3_1aPpParser::RuleTimescale_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(367);
    match(SV3_1aPpParser::TICK_TIMESCALE);
    setState(368);
    match(SV3_1aPpParser::TIMESCALE);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Undef_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Undef_directiveContext::Undef_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Undef_directiveContext::TICK_UNDEF() {
  return getToken(SV3_1aPpParser::TICK_UNDEF, 0);
}

tree::TerminalNode* SV3_1aPpParser::Undef_directiveContext::Spaces() {
  return getToken(SV3_1aPpParser::Spaces, 0);
}

tree::TerminalNode* SV3_1aPpParser::Undef_directiveContext::Simple_identifier() {
  return getToken(SV3_1aPpParser::Simple_identifier, 0);
}

tree::TerminalNode* SV3_1aPpParser::Undef_directiveContext::Escaped_identifier() {
  return getToken(SV3_1aPpParser::Escaped_identifier, 0);
}

SV3_1aPpParser::Macro_instanceContext* SV3_1aPpParser::Undef_directiveContext::macro_instance() {
  return getRuleContext<SV3_1aPpParser::Macro_instanceContext>(0);
}


size_t SV3_1aPpParser::Undef_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleUndef_directive;
}

void SV3_1aPpParser::Undef_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterUndef_directive(this);
}

void SV3_1aPpParser::Undef_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitUndef_directive(this);
}

SV3_1aPpParser::Undef_directiveContext* SV3_1aPpParser::undef_directive() {
  Undef_directiveContext *_localctx = _tracker.createInstance<Undef_directiveContext>(_ctx, getState());
  enterRule(_localctx, 36, SV3_1aPpParser::RuleUndef_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(370);
    match(SV3_1aPpParser::TICK_UNDEF);
    setState(371);
    match(SV3_1aPpParser::Spaces);
    setState(375);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case SV3_1aPpParser::Simple_identifier: {
        setState(372);
        match(SV3_1aPpParser::Simple_identifier);
        break;
      }

      case SV3_1aPpParser::Escaped_identifier: {
        setState(373);
        match(SV3_1aPpParser::Escaped_identifier);
        break;
      }

      case SV3_1aPpParser::Macro_identifier:
      case SV3_1aPpParser::Macro_Escaped_identifier: {
        setState(374);
        macro_instance();
        break;
      }

    default:
      throw NoViableAltException(this);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Ifdef_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Ifdef_directiveContext::Ifdef_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Ifdef_directiveContext::TICK_IFDEF() {
  return getToken(SV3_1aPpParser::TICK_IFDEF, 0);
}

tree::TerminalNode* SV3_1aPpParser::Ifdef_directiveContext::Spaces() {
  return getToken(SV3_1aPpParser::Spaces, 0);
}

tree::TerminalNode* SV3_1aPpParser::Ifdef_directiveContext::Simple_identifier() {
  return getToken(SV3_1aPpParser::Simple_identifier, 0);
}

tree::TerminalNode* SV3_1aPpParser::Ifdef_directiveContext::Escaped_identifier() {
  return getToken(SV3_1aPpParser::Escaped_identifier, 0);
}

SV3_1aPpParser::Macro_instanceContext* SV3_1aPpParser::Ifdef_directiveContext::macro_instance() {
  return getRuleContext<SV3_1aPpParser::Macro_instanceContext>(0);
}


size_t SV3_1aPpParser::Ifdef_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleIfdef_directive;
}

void SV3_1aPpParser::Ifdef_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterIfdef_directive(this);
}

void SV3_1aPpParser::Ifdef_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitIfdef_directive(this);
}

SV3_1aPpParser::Ifdef_directiveContext* SV3_1aPpParser::ifdef_directive() {
  Ifdef_directiveContext *_localctx = _tracker.createInstance<Ifdef_directiveContext>(_ctx, getState());
  enterRule(_localctx, 38, SV3_1aPpParser::RuleIfdef_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(377);
    match(SV3_1aPpParser::TICK_IFDEF);
    setState(378);
    match(SV3_1aPpParser::Spaces);
    setState(382);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case SV3_1aPpParser::Simple_identifier: {
        setState(379);
        match(SV3_1aPpParser::Simple_identifier);
        break;
      }

      case SV3_1aPpParser::Escaped_identifier: {
        setState(380);
        match(SV3_1aPpParser::Escaped_identifier);
        break;
      }

      case SV3_1aPpParser::Macro_identifier:
      case SV3_1aPpParser::Macro_Escaped_identifier: {
        setState(381);
        macro_instance();
        break;
      }

    default:
      throw NoViableAltException(this);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Ifdef_directive_in_macro_bodyContext ------------------------------------------------------------------

SV3_1aPpParser::Ifdef_directive_in_macro_bodyContext::Ifdef_directive_in_macro_bodyContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Ifdef_directive_in_macro_bodyContext::TICK_IFDEF() {
  return getToken(SV3_1aPpParser::TICK_IFDEF, 0);
}

tree::TerminalNode* SV3_1aPpParser::Ifdef_directive_in_macro_bodyContext::Spaces() {
  return getToken(SV3_1aPpParser::Spaces, 0);
}

SV3_1aPpParser::Identifier_in_macro_bodyContext* SV3_1aPpParser::Ifdef_directive_in_macro_bodyContext::identifier_in_macro_body() {
  return getRuleContext<SV3_1aPpParser::Identifier_in_macro_bodyContext>(0);
}

tree::TerminalNode* SV3_1aPpParser::Ifdef_directive_in_macro_bodyContext::Escaped_identifier() {
  return getToken(SV3_1aPpParser::Escaped_identifier, 0);
}

SV3_1aPpParser::Macro_instanceContext* SV3_1aPpParser::Ifdef_directive_in_macro_bodyContext::macro_instance() {
  return getRuleContext<SV3_1aPpParser::Macro_instanceContext>(0);
}


size_t SV3_1aPpParser::Ifdef_directive_in_macro_bodyContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleIfdef_directive_in_macro_body;
}

void SV3_1aPpParser::Ifdef_directive_in_macro_bodyContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterIfdef_directive_in_macro_body(this);
}

void SV3_1aPpParser::Ifdef_directive_in_macro_bodyContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitIfdef_directive_in_macro_body(this);
}

SV3_1aPpParser::Ifdef_directive_in_macro_bodyContext* SV3_1aPpParser::ifdef_directive_in_macro_body() {
  Ifdef_directive_in_macro_bodyContext *_localctx = _tracker.createInstance<Ifdef_directive_in_macro_bodyContext>(_ctx, getState());
  enterRule(_localctx, 40, SV3_1aPpParser::RuleIfdef_directive_in_macro_body);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(384);
    match(SV3_1aPpParser::TICK_IFDEF);
    setState(385);
    match(SV3_1aPpParser::Spaces);
    setState(389);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case SV3_1aPpParser::EOF:
      case SV3_1aPpParser::Simple_identifier: {
        setState(386);
        identifier_in_macro_body();
        break;
      }

      case SV3_1aPpParser::Escaped_identifier: {
        setState(387);
        match(SV3_1aPpParser::Escaped_identifier);
        break;
      }

      case SV3_1aPpParser::Macro_identifier:
      case SV3_1aPpParser::Macro_Escaped_identifier: {
        setState(388);
        macro_instance();
        break;
      }

    default:
      throw NoViableAltException(this);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Ifndef_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Ifndef_directiveContext::Ifndef_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Ifndef_directiveContext::TICK_IFNDEF() {
  return getToken(SV3_1aPpParser::TICK_IFNDEF, 0);
}

tree::TerminalNode* SV3_1aPpParser::Ifndef_directiveContext::Spaces() {
  return getToken(SV3_1aPpParser::Spaces, 0);
}

tree::TerminalNode* SV3_1aPpParser::Ifndef_directiveContext::Simple_identifier() {
  return getToken(SV3_1aPpParser::Simple_identifier, 0);
}

tree::TerminalNode* SV3_1aPpParser::Ifndef_directiveContext::Escaped_identifier() {
  return getToken(SV3_1aPpParser::Escaped_identifier, 0);
}

SV3_1aPpParser::Macro_instanceContext* SV3_1aPpParser::Ifndef_directiveContext::macro_instance() {
  return getRuleContext<SV3_1aPpParser::Macro_instanceContext>(0);
}


size_t SV3_1aPpParser::Ifndef_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleIfndef_directive;
}

void SV3_1aPpParser::Ifndef_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterIfndef_directive(this);
}

void SV3_1aPpParser::Ifndef_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitIfndef_directive(this);
}

SV3_1aPpParser::Ifndef_directiveContext* SV3_1aPpParser::ifndef_directive() {
  Ifndef_directiveContext *_localctx = _tracker.createInstance<Ifndef_directiveContext>(_ctx, getState());
  enterRule(_localctx, 42, SV3_1aPpParser::RuleIfndef_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(391);
    match(SV3_1aPpParser::TICK_IFNDEF);
    setState(392);
    match(SV3_1aPpParser::Spaces);
    setState(396);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case SV3_1aPpParser::Simple_identifier: {
        setState(393);
        match(SV3_1aPpParser::Simple_identifier);
        break;
      }

      case SV3_1aPpParser::Escaped_identifier: {
        setState(394);
        match(SV3_1aPpParser::Escaped_identifier);
        break;
      }

      case SV3_1aPpParser::Macro_identifier:
      case SV3_1aPpParser::Macro_Escaped_identifier: {
        setState(395);
        macro_instance();
        break;
      }

    default:
      throw NoViableAltException(this);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Ifndef_directive_in_macro_bodyContext ------------------------------------------------------------------

SV3_1aPpParser::Ifndef_directive_in_macro_bodyContext::Ifndef_directive_in_macro_bodyContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Ifndef_directive_in_macro_bodyContext::TICK_IFNDEF() {
  return getToken(SV3_1aPpParser::TICK_IFNDEF, 0);
}

tree::TerminalNode* SV3_1aPpParser::Ifndef_directive_in_macro_bodyContext::Spaces() {
  return getToken(SV3_1aPpParser::Spaces, 0);
}

SV3_1aPpParser::Identifier_in_macro_bodyContext* SV3_1aPpParser::Ifndef_directive_in_macro_bodyContext::identifier_in_macro_body() {
  return getRuleContext<SV3_1aPpParser::Identifier_in_macro_bodyContext>(0);
}

tree::TerminalNode* SV3_1aPpParser::Ifndef_directive_in_macro_bodyContext::Escaped_identifier() {
  return getToken(SV3_1aPpParser::Escaped_identifier, 0);
}

SV3_1aPpParser::Macro_instanceContext* SV3_1aPpParser::Ifndef_directive_in_macro_bodyContext::macro_instance() {
  return getRuleContext<SV3_1aPpParser::Macro_instanceContext>(0);
}


size_t SV3_1aPpParser::Ifndef_directive_in_macro_bodyContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleIfndef_directive_in_macro_body;
}

void SV3_1aPpParser::Ifndef_directive_in_macro_bodyContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterIfndef_directive_in_macro_body(this);
}

void SV3_1aPpParser::Ifndef_directive_in_macro_bodyContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitIfndef_directive_in_macro_body(this);
}

SV3_1aPpParser::Ifndef_directive_in_macro_bodyContext* SV3_1aPpParser::ifndef_directive_in_macro_body() {
  Ifndef_directive_in_macro_bodyContext *_localctx = _tracker.createInstance<Ifndef_directive_in_macro_bodyContext>(_ctx, getState());
  enterRule(_localctx, 44, SV3_1aPpParser::RuleIfndef_directive_in_macro_body);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(398);
    match(SV3_1aPpParser::TICK_IFNDEF);
    setState(399);
    match(SV3_1aPpParser::Spaces);
    setState(403);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case SV3_1aPpParser::EOF:
      case SV3_1aPpParser::Simple_identifier: {
        setState(400);
        identifier_in_macro_body();
        break;
      }

      case SV3_1aPpParser::Escaped_identifier: {
        setState(401);
        match(SV3_1aPpParser::Escaped_identifier);
        break;
      }

      case SV3_1aPpParser::Macro_identifier:
      case SV3_1aPpParser::Macro_Escaped_identifier: {
        setState(402);
        macro_instance();
        break;
      }

    default:
      throw NoViableAltException(this);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Elsif_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Elsif_directiveContext::Elsif_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Elsif_directiveContext::TICK_ELSIF() {
  return getToken(SV3_1aPpParser::TICK_ELSIF, 0);
}

tree::TerminalNode* SV3_1aPpParser::Elsif_directiveContext::Spaces() {
  return getToken(SV3_1aPpParser::Spaces, 0);
}

tree::TerminalNode* SV3_1aPpParser::Elsif_directiveContext::Simple_identifier() {
  return getToken(SV3_1aPpParser::Simple_identifier, 0);
}

tree::TerminalNode* SV3_1aPpParser::Elsif_directiveContext::Escaped_identifier() {
  return getToken(SV3_1aPpParser::Escaped_identifier, 0);
}

SV3_1aPpParser::Macro_instanceContext* SV3_1aPpParser::Elsif_directiveContext::macro_instance() {
  return getRuleContext<SV3_1aPpParser::Macro_instanceContext>(0);
}


size_t SV3_1aPpParser::Elsif_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleElsif_directive;
}

void SV3_1aPpParser::Elsif_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterElsif_directive(this);
}

void SV3_1aPpParser::Elsif_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitElsif_directive(this);
}

SV3_1aPpParser::Elsif_directiveContext* SV3_1aPpParser::elsif_directive() {
  Elsif_directiveContext *_localctx = _tracker.createInstance<Elsif_directiveContext>(_ctx, getState());
  enterRule(_localctx, 46, SV3_1aPpParser::RuleElsif_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(405);
    match(SV3_1aPpParser::TICK_ELSIF);
    setState(406);
    match(SV3_1aPpParser::Spaces);
    setState(410);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case SV3_1aPpParser::Simple_identifier: {
        setState(407);
        match(SV3_1aPpParser::Simple_identifier);
        break;
      }

      case SV3_1aPpParser::Escaped_identifier: {
        setState(408);
        match(SV3_1aPpParser::Escaped_identifier);
        break;
      }

      case SV3_1aPpParser::Macro_identifier:
      case SV3_1aPpParser::Macro_Escaped_identifier: {
        setState(409);
        macro_instance();
        break;
      }

    default:
      throw NoViableAltException(this);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Elsif_directive_in_macro_bodyContext ------------------------------------------------------------------

SV3_1aPpParser::Elsif_directive_in_macro_bodyContext::Elsif_directive_in_macro_bodyContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Elsif_directive_in_macro_bodyContext::TICK_ELSIF() {
  return getToken(SV3_1aPpParser::TICK_ELSIF, 0);
}

tree::TerminalNode* SV3_1aPpParser::Elsif_directive_in_macro_bodyContext::Spaces() {
  return getToken(SV3_1aPpParser::Spaces, 0);
}

SV3_1aPpParser::Identifier_in_macro_bodyContext* SV3_1aPpParser::Elsif_directive_in_macro_bodyContext::identifier_in_macro_body() {
  return getRuleContext<SV3_1aPpParser::Identifier_in_macro_bodyContext>(0);
}

tree::TerminalNode* SV3_1aPpParser::Elsif_directive_in_macro_bodyContext::Escaped_identifier() {
  return getToken(SV3_1aPpParser::Escaped_identifier, 0);
}

SV3_1aPpParser::Macro_instanceContext* SV3_1aPpParser::Elsif_directive_in_macro_bodyContext::macro_instance() {
  return getRuleContext<SV3_1aPpParser::Macro_instanceContext>(0);
}


size_t SV3_1aPpParser::Elsif_directive_in_macro_bodyContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleElsif_directive_in_macro_body;
}

void SV3_1aPpParser::Elsif_directive_in_macro_bodyContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterElsif_directive_in_macro_body(this);
}

void SV3_1aPpParser::Elsif_directive_in_macro_bodyContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitElsif_directive_in_macro_body(this);
}

SV3_1aPpParser::Elsif_directive_in_macro_bodyContext* SV3_1aPpParser::elsif_directive_in_macro_body() {
  Elsif_directive_in_macro_bodyContext *_localctx = _tracker.createInstance<Elsif_directive_in_macro_bodyContext>(_ctx, getState());
  enterRule(_localctx, 48, SV3_1aPpParser::RuleElsif_directive_in_macro_body);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(412);
    match(SV3_1aPpParser::TICK_ELSIF);
    setState(413);
    match(SV3_1aPpParser::Spaces);
    setState(417);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case SV3_1aPpParser::EOF:
      case SV3_1aPpParser::Simple_identifier: {
        setState(414);
        identifier_in_macro_body();
        break;
      }

      case SV3_1aPpParser::Escaped_identifier: {
        setState(415);
        match(SV3_1aPpParser::Escaped_identifier);
        break;
      }

      case SV3_1aPpParser::Macro_identifier:
      case SV3_1aPpParser::Macro_Escaped_identifier: {
        setState(416);
        macro_instance();
        break;
      }

    default:
      throw NoViableAltException(this);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Elseif_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Elseif_directiveContext::Elseif_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Elseif_directiveContext::TICK_ELSEIF() {
  return getToken(SV3_1aPpParser::TICK_ELSEIF, 0);
}

tree::TerminalNode* SV3_1aPpParser::Elseif_directiveContext::Spaces() {
  return getToken(SV3_1aPpParser::Spaces, 0);
}

tree::TerminalNode* SV3_1aPpParser::Elseif_directiveContext::Simple_identifier() {
  return getToken(SV3_1aPpParser::Simple_identifier, 0);
}

tree::TerminalNode* SV3_1aPpParser::Elseif_directiveContext::Escaped_identifier() {
  return getToken(SV3_1aPpParser::Escaped_identifier, 0);
}

SV3_1aPpParser::Macro_instanceContext* SV3_1aPpParser::Elseif_directiveContext::macro_instance() {
  return getRuleContext<SV3_1aPpParser::Macro_instanceContext>(0);
}


size_t SV3_1aPpParser::Elseif_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleElseif_directive;
}

void SV3_1aPpParser::Elseif_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterElseif_directive(this);
}

void SV3_1aPpParser::Elseif_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitElseif_directive(this);
}

SV3_1aPpParser::Elseif_directiveContext* SV3_1aPpParser::elseif_directive() {
  Elseif_directiveContext *_localctx = _tracker.createInstance<Elseif_directiveContext>(_ctx, getState());
  enterRule(_localctx, 50, SV3_1aPpParser::RuleElseif_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(419);
    match(SV3_1aPpParser::TICK_ELSEIF);
    setState(420);
    match(SV3_1aPpParser::Spaces);
    setState(424);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case SV3_1aPpParser::Simple_identifier: {
        setState(421);
        match(SV3_1aPpParser::Simple_identifier);
        break;
      }

      case SV3_1aPpParser::Escaped_identifier: {
        setState(422);
        match(SV3_1aPpParser::Escaped_identifier);
        break;
      }

      case SV3_1aPpParser::Macro_identifier:
      case SV3_1aPpParser::Macro_Escaped_identifier: {
        setState(423);
        macro_instance();
        break;
      }

    default:
      throw NoViableAltException(this);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Elseif_directive_in_macro_bodyContext ------------------------------------------------------------------

SV3_1aPpParser::Elseif_directive_in_macro_bodyContext::Elseif_directive_in_macro_bodyContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Elseif_directive_in_macro_bodyContext::TICK_ELSEIF() {
  return getToken(SV3_1aPpParser::TICK_ELSEIF, 0);
}

tree::TerminalNode* SV3_1aPpParser::Elseif_directive_in_macro_bodyContext::Spaces() {
  return getToken(SV3_1aPpParser::Spaces, 0);
}

SV3_1aPpParser::Identifier_in_macro_bodyContext* SV3_1aPpParser::Elseif_directive_in_macro_bodyContext::identifier_in_macro_body() {
  return getRuleContext<SV3_1aPpParser::Identifier_in_macro_bodyContext>(0);
}

tree::TerminalNode* SV3_1aPpParser::Elseif_directive_in_macro_bodyContext::Escaped_identifier() {
  return getToken(SV3_1aPpParser::Escaped_identifier, 0);
}

SV3_1aPpParser::Macro_instanceContext* SV3_1aPpParser::Elseif_directive_in_macro_bodyContext::macro_instance() {
  return getRuleContext<SV3_1aPpParser::Macro_instanceContext>(0);
}


size_t SV3_1aPpParser::Elseif_directive_in_macro_bodyContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleElseif_directive_in_macro_body;
}

void SV3_1aPpParser::Elseif_directive_in_macro_bodyContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterElseif_directive_in_macro_body(this);
}

void SV3_1aPpParser::Elseif_directive_in_macro_bodyContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitElseif_directive_in_macro_body(this);
}

SV3_1aPpParser::Elseif_directive_in_macro_bodyContext* SV3_1aPpParser::elseif_directive_in_macro_body() {
  Elseif_directive_in_macro_bodyContext *_localctx = _tracker.createInstance<Elseif_directive_in_macro_bodyContext>(_ctx, getState());
  enterRule(_localctx, 52, SV3_1aPpParser::RuleElseif_directive_in_macro_body);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(426);
    match(SV3_1aPpParser::TICK_ELSEIF);
    setState(427);
    match(SV3_1aPpParser::Spaces);
    setState(431);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case SV3_1aPpParser::EOF:
      case SV3_1aPpParser::Simple_identifier: {
        setState(428);
        identifier_in_macro_body();
        break;
      }

      case SV3_1aPpParser::Escaped_identifier: {
        setState(429);
        match(SV3_1aPpParser::Escaped_identifier);
        break;
      }

      case SV3_1aPpParser::Macro_identifier:
      case SV3_1aPpParser::Macro_Escaped_identifier: {
        setState(430);
        macro_instance();
        break;
      }

    default:
      throw NoViableAltException(this);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Else_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Else_directiveContext::Else_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Else_directiveContext::TICK_ELSE() {
  return getToken(SV3_1aPpParser::TICK_ELSE, 0);
}


size_t SV3_1aPpParser::Else_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleElse_directive;
}

void SV3_1aPpParser::Else_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterElse_directive(this);
}

void SV3_1aPpParser::Else_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitElse_directive(this);
}

SV3_1aPpParser::Else_directiveContext* SV3_1aPpParser::else_directive() {
  Else_directiveContext *_localctx = _tracker.createInstance<Else_directiveContext>(_ctx, getState());
  enterRule(_localctx, 54, SV3_1aPpParser::RuleElse_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(433);
    match(SV3_1aPpParser::TICK_ELSE);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Endif_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Endif_directiveContext::Endif_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Endif_directiveContext::TICK_ENDIF() {
  return getToken(SV3_1aPpParser::TICK_ENDIF, 0);
}

tree::TerminalNode* SV3_1aPpParser::Endif_directiveContext::One_line_comment() {
  return getToken(SV3_1aPpParser::One_line_comment, 0);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Endif_directiveContext::Spaces() {
  return getTokens(SV3_1aPpParser::Spaces);
}

tree::TerminalNode* SV3_1aPpParser::Endif_directiveContext::Spaces(size_t i) {
  return getToken(SV3_1aPpParser::Spaces, i);
}


size_t SV3_1aPpParser::Endif_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleEndif_directive;
}

void SV3_1aPpParser::Endif_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterEndif_directive(this);
}

void SV3_1aPpParser::Endif_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitEndif_directive(this);
}

SV3_1aPpParser::Endif_directiveContext* SV3_1aPpParser::endif_directive() {
  Endif_directiveContext *_localctx = _tracker.createInstance<Endif_directiveContext>(_ctx, getState());
  enterRule(_localctx, 56, SV3_1aPpParser::RuleEndif_directive);
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    setState(444);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 20, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(435);
      match(SV3_1aPpParser::TICK_ENDIF);
      setState(439);
      _errHandler->sync(this);
      _la = _input->LA(1);
      while (_la == SV3_1aPpParser::Spaces) {
        setState(436);
        match(SV3_1aPpParser::Spaces);
        setState(441);
        _errHandler->sync(this);
        _la = _input->LA(1);
      }
      setState(442);
      match(SV3_1aPpParser::One_line_comment);
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(443);
      match(SV3_1aPpParser::TICK_ENDIF);
      break;
    }

    default:
      break;
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Resetall_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Resetall_directiveContext::Resetall_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Resetall_directiveContext::TICK_RESETALL() {
  return getToken(SV3_1aPpParser::TICK_RESETALL, 0);
}


size_t SV3_1aPpParser::Resetall_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleResetall_directive;
}

void SV3_1aPpParser::Resetall_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterResetall_directive(this);
}

void SV3_1aPpParser::Resetall_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitResetall_directive(this);
}

SV3_1aPpParser::Resetall_directiveContext* SV3_1aPpParser::resetall_directive() {
  Resetall_directiveContext *_localctx = _tracker.createInstance<Resetall_directiveContext>(_ctx, getState());
  enterRule(_localctx, 58, SV3_1aPpParser::RuleResetall_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(446);
    match(SV3_1aPpParser::TICK_RESETALL);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Begin_keywords_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Begin_keywords_directiveContext::Begin_keywords_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Begin_keywords_directiveContext::TICK_BEGIN_KEYWORDS() {
  return getToken(SV3_1aPpParser::TICK_BEGIN_KEYWORDS, 0);
}

tree::TerminalNode* SV3_1aPpParser::Begin_keywords_directiveContext::Spaces() {
  return getToken(SV3_1aPpParser::Spaces, 0);
}

tree::TerminalNode* SV3_1aPpParser::Begin_keywords_directiveContext::String() {
  return getToken(SV3_1aPpParser::String, 0);
}


size_t SV3_1aPpParser::Begin_keywords_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleBegin_keywords_directive;
}

void SV3_1aPpParser::Begin_keywords_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterBegin_keywords_directive(this);
}

void SV3_1aPpParser::Begin_keywords_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitBegin_keywords_directive(this);
}

SV3_1aPpParser::Begin_keywords_directiveContext* SV3_1aPpParser::begin_keywords_directive() {
  Begin_keywords_directiveContext *_localctx = _tracker.createInstance<Begin_keywords_directiveContext>(_ctx, getState());
  enterRule(_localctx, 60, SV3_1aPpParser::RuleBegin_keywords_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(448);
    match(SV3_1aPpParser::TICK_BEGIN_KEYWORDS);
    setState(449);
    match(SV3_1aPpParser::Spaces);
    setState(450);
    match(SV3_1aPpParser::String);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- End_keywords_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::End_keywords_directiveContext::End_keywords_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::End_keywords_directiveContext::TICK_END_KEYWORDS() {
  return getToken(SV3_1aPpParser::TICK_END_KEYWORDS, 0);
}


size_t SV3_1aPpParser::End_keywords_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleEnd_keywords_directive;
}

void SV3_1aPpParser::End_keywords_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterEnd_keywords_directive(this);
}

void SV3_1aPpParser::End_keywords_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitEnd_keywords_directive(this);
}

SV3_1aPpParser::End_keywords_directiveContext* SV3_1aPpParser::end_keywords_directive() {
  End_keywords_directiveContext *_localctx = _tracker.createInstance<End_keywords_directiveContext>(_ctx, getState());
  enterRule(_localctx, 62, SV3_1aPpParser::RuleEnd_keywords_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(452);
    match(SV3_1aPpParser::TICK_END_KEYWORDS);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Pragma_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Pragma_directiveContext::Pragma_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Pragma_directiveContext::TICK_PRAGMA() {
  return getToken(SV3_1aPpParser::TICK_PRAGMA, 0);
}

tree::TerminalNode* SV3_1aPpParser::Pragma_directiveContext::Spaces() {
  return getToken(SV3_1aPpParser::Spaces, 0);
}

tree::TerminalNode* SV3_1aPpParser::Pragma_directiveContext::Simple_identifier() {
  return getToken(SV3_1aPpParser::Simple_identifier, 0);
}

std::vector<SV3_1aPpParser::Pragma_expressionContext *> SV3_1aPpParser::Pragma_directiveContext::pragma_expression() {
  return getRuleContexts<SV3_1aPpParser::Pragma_expressionContext>();
}

SV3_1aPpParser::Pragma_expressionContext* SV3_1aPpParser::Pragma_directiveContext::pragma_expression(size_t i) {
  return getRuleContext<SV3_1aPpParser::Pragma_expressionContext>(i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Pragma_directiveContext::Special() {
  return getTokens(SV3_1aPpParser::Special);
}

tree::TerminalNode* SV3_1aPpParser::Pragma_directiveContext::Special(size_t i) {
  return getToken(SV3_1aPpParser::Special, i);
}


size_t SV3_1aPpParser::Pragma_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RulePragma_directive;
}

void SV3_1aPpParser::Pragma_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterPragma_directive(this);
}

void SV3_1aPpParser::Pragma_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitPragma_directive(this);
}

SV3_1aPpParser::Pragma_directiveContext* SV3_1aPpParser::pragma_directive() {
  Pragma_directiveContext *_localctx = _tracker.createInstance<Pragma_directiveContext>(_ctx, getState());
  enterRule(_localctx, 64, SV3_1aPpParser::RulePragma_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    size_t alt;
    enterOuterAlt(_localctx, 1);
    setState(454);
    match(SV3_1aPpParser::TICK_PRAGMA);
    setState(455);
    match(SV3_1aPpParser::Spaces);
    setState(456);
    match(SV3_1aPpParser::Simple_identifier);
    setState(467);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 22, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        setState(457);
        pragma_expression();
        setState(462);
        _errHandler->sync(this);
        alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 21, _ctx);
        while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
          if (alt == 1) {
            setState(458);
            match(SV3_1aPpParser::Special);
            setState(459);
            pragma_expression(); 
          }
          setState(464);
          _errHandler->sync(this);
          alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 21, _ctx);
        } 
      }
      setState(469);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 22, _ctx);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Celldefine_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Celldefine_directiveContext::Celldefine_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Celldefine_directiveContext::TICK_CELLDEFINE() {
  return getToken(SV3_1aPpParser::TICK_CELLDEFINE, 0);
}

tree::TerminalNode* SV3_1aPpParser::Celldefine_directiveContext::CR() {
  return getToken(SV3_1aPpParser::CR, 0);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Celldefine_directiveContext::Spaces() {
  return getTokens(SV3_1aPpParser::Spaces);
}

tree::TerminalNode* SV3_1aPpParser::Celldefine_directiveContext::Spaces(size_t i) {
  return getToken(SV3_1aPpParser::Spaces, i);
}


size_t SV3_1aPpParser::Celldefine_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleCelldefine_directive;
}

void SV3_1aPpParser::Celldefine_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterCelldefine_directive(this);
}

void SV3_1aPpParser::Celldefine_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitCelldefine_directive(this);
}

SV3_1aPpParser::Celldefine_directiveContext* SV3_1aPpParser::celldefine_directive() {
  Celldefine_directiveContext *_localctx = _tracker.createInstance<Celldefine_directiveContext>(_ctx, getState());
  enterRule(_localctx, 66, SV3_1aPpParser::RuleCelldefine_directive);
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(470);
    match(SV3_1aPpParser::TICK_CELLDEFINE);
    setState(474);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (_la == SV3_1aPpParser::Spaces) {
      setState(471);
      match(SV3_1aPpParser::Spaces);
      setState(476);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
    setState(477);
    match(SV3_1aPpParser::CR);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Endcelldefine_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Endcelldefine_directiveContext::Endcelldefine_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Endcelldefine_directiveContext::TICK_ENDCELLDEFINE() {
  return getToken(SV3_1aPpParser::TICK_ENDCELLDEFINE, 0);
}

tree::TerminalNode* SV3_1aPpParser::Endcelldefine_directiveContext::CR() {
  return getToken(SV3_1aPpParser::CR, 0);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Endcelldefine_directiveContext::Spaces() {
  return getTokens(SV3_1aPpParser::Spaces);
}

tree::TerminalNode* SV3_1aPpParser::Endcelldefine_directiveContext::Spaces(size_t i) {
  return getToken(SV3_1aPpParser::Spaces, i);
}


size_t SV3_1aPpParser::Endcelldefine_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleEndcelldefine_directive;
}

void SV3_1aPpParser::Endcelldefine_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterEndcelldefine_directive(this);
}

void SV3_1aPpParser::Endcelldefine_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitEndcelldefine_directive(this);
}

SV3_1aPpParser::Endcelldefine_directiveContext* SV3_1aPpParser::endcelldefine_directive() {
  Endcelldefine_directiveContext *_localctx = _tracker.createInstance<Endcelldefine_directiveContext>(_ctx, getState());
  enterRule(_localctx, 68, SV3_1aPpParser::RuleEndcelldefine_directive);
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(479);
    match(SV3_1aPpParser::TICK_ENDCELLDEFINE);
    setState(483);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (_la == SV3_1aPpParser::Spaces) {
      setState(480);
      match(SV3_1aPpParser::Spaces);
      setState(485);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
    setState(486);
    match(SV3_1aPpParser::CR);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Protect_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Protect_directiveContext::Protect_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Protect_directiveContext::TICK_PROTECT() {
  return getToken(SV3_1aPpParser::TICK_PROTECT, 0);
}

tree::TerminalNode* SV3_1aPpParser::Protect_directiveContext::CR() {
  return getToken(SV3_1aPpParser::CR, 0);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Protect_directiveContext::Spaces() {
  return getTokens(SV3_1aPpParser::Spaces);
}

tree::TerminalNode* SV3_1aPpParser::Protect_directiveContext::Spaces(size_t i) {
  return getToken(SV3_1aPpParser::Spaces, i);
}


size_t SV3_1aPpParser::Protect_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleProtect_directive;
}

void SV3_1aPpParser::Protect_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterProtect_directive(this);
}

void SV3_1aPpParser::Protect_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitProtect_directive(this);
}

SV3_1aPpParser::Protect_directiveContext* SV3_1aPpParser::protect_directive() {
  Protect_directiveContext *_localctx = _tracker.createInstance<Protect_directiveContext>(_ctx, getState());
  enterRule(_localctx, 70, SV3_1aPpParser::RuleProtect_directive);
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(488);
    match(SV3_1aPpParser::TICK_PROTECT);
    setState(492);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (_la == SV3_1aPpParser::Spaces) {
      setState(489);
      match(SV3_1aPpParser::Spaces);
      setState(494);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
    setState(495);
    match(SV3_1aPpParser::CR);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Endprotect_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Endprotect_directiveContext::Endprotect_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Endprotect_directiveContext::TICK_ENDPROTECT() {
  return getToken(SV3_1aPpParser::TICK_ENDPROTECT, 0);
}

tree::TerminalNode* SV3_1aPpParser::Endprotect_directiveContext::CR() {
  return getToken(SV3_1aPpParser::CR, 0);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Endprotect_directiveContext::Spaces() {
  return getTokens(SV3_1aPpParser::Spaces);
}

tree::TerminalNode* SV3_1aPpParser::Endprotect_directiveContext::Spaces(size_t i) {
  return getToken(SV3_1aPpParser::Spaces, i);
}


size_t SV3_1aPpParser::Endprotect_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleEndprotect_directive;
}

void SV3_1aPpParser::Endprotect_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterEndprotect_directive(this);
}

void SV3_1aPpParser::Endprotect_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitEndprotect_directive(this);
}

SV3_1aPpParser::Endprotect_directiveContext* SV3_1aPpParser::endprotect_directive() {
  Endprotect_directiveContext *_localctx = _tracker.createInstance<Endprotect_directiveContext>(_ctx, getState());
  enterRule(_localctx, 72, SV3_1aPpParser::RuleEndprotect_directive);
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(497);
    match(SV3_1aPpParser::TICK_ENDPROTECT);
    setState(501);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (_la == SV3_1aPpParser::Spaces) {
      setState(498);
      match(SV3_1aPpParser::Spaces);
      setState(503);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
    setState(504);
    match(SV3_1aPpParser::CR);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Protected_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Protected_directiveContext::Protected_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Protected_directiveContext::TICK_PROTECTED() {
  return getToken(SV3_1aPpParser::TICK_PROTECTED, 0);
}


size_t SV3_1aPpParser::Protected_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleProtected_directive;
}

void SV3_1aPpParser::Protected_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterProtected_directive(this);
}

void SV3_1aPpParser::Protected_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitProtected_directive(this);
}

SV3_1aPpParser::Protected_directiveContext* SV3_1aPpParser::protected_directive() {
  Protected_directiveContext *_localctx = _tracker.createInstance<Protected_directiveContext>(_ctx, getState());
  enterRule(_localctx, 74, SV3_1aPpParser::RuleProtected_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(506);
    match(SV3_1aPpParser::TICK_PROTECTED);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Endprotected_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Endprotected_directiveContext::Endprotected_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Endprotected_directiveContext::TICK_ENDPROTECTED() {
  return getToken(SV3_1aPpParser::TICK_ENDPROTECTED, 0);
}


size_t SV3_1aPpParser::Endprotected_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleEndprotected_directive;
}

void SV3_1aPpParser::Endprotected_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterEndprotected_directive(this);
}

void SV3_1aPpParser::Endprotected_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitEndprotected_directive(this);
}

SV3_1aPpParser::Endprotected_directiveContext* SV3_1aPpParser::endprotected_directive() {
  Endprotected_directiveContext *_localctx = _tracker.createInstance<Endprotected_directiveContext>(_ctx, getState());
  enterRule(_localctx, 76, SV3_1aPpParser::RuleEndprotected_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(508);
    match(SV3_1aPpParser::TICK_ENDPROTECTED);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Expand_vectornets_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Expand_vectornets_directiveContext::Expand_vectornets_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Expand_vectornets_directiveContext::TICK_EXPAND_VECTORNETS() {
  return getToken(SV3_1aPpParser::TICK_EXPAND_VECTORNETS, 0);
}


size_t SV3_1aPpParser::Expand_vectornets_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleExpand_vectornets_directive;
}

void SV3_1aPpParser::Expand_vectornets_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterExpand_vectornets_directive(this);
}

void SV3_1aPpParser::Expand_vectornets_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitExpand_vectornets_directive(this);
}

SV3_1aPpParser::Expand_vectornets_directiveContext* SV3_1aPpParser::expand_vectornets_directive() {
  Expand_vectornets_directiveContext *_localctx = _tracker.createInstance<Expand_vectornets_directiveContext>(_ctx, getState());
  enterRule(_localctx, 78, SV3_1aPpParser::RuleExpand_vectornets_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(510);
    match(SV3_1aPpParser::TICK_EXPAND_VECTORNETS);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Noexpand_vectornets_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Noexpand_vectornets_directiveContext::Noexpand_vectornets_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Noexpand_vectornets_directiveContext::TICK_NOEXPAND_VECTORNETS() {
  return getToken(SV3_1aPpParser::TICK_NOEXPAND_VECTORNETS, 0);
}


size_t SV3_1aPpParser::Noexpand_vectornets_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleNoexpand_vectornets_directive;
}

void SV3_1aPpParser::Noexpand_vectornets_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterNoexpand_vectornets_directive(this);
}

void SV3_1aPpParser::Noexpand_vectornets_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitNoexpand_vectornets_directive(this);
}

SV3_1aPpParser::Noexpand_vectornets_directiveContext* SV3_1aPpParser::noexpand_vectornets_directive() {
  Noexpand_vectornets_directiveContext *_localctx = _tracker.createInstance<Noexpand_vectornets_directiveContext>(_ctx, getState());
  enterRule(_localctx, 80, SV3_1aPpParser::RuleNoexpand_vectornets_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(512);
    match(SV3_1aPpParser::TICK_NOEXPAND_VECTORNETS);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Autoexpand_vectornets_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Autoexpand_vectornets_directiveContext::Autoexpand_vectornets_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Autoexpand_vectornets_directiveContext::TICK_AUTOEXPAND_VECTORNETS() {
  return getToken(SV3_1aPpParser::TICK_AUTOEXPAND_VECTORNETS, 0);
}


size_t SV3_1aPpParser::Autoexpand_vectornets_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleAutoexpand_vectornets_directive;
}

void SV3_1aPpParser::Autoexpand_vectornets_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterAutoexpand_vectornets_directive(this);
}

void SV3_1aPpParser::Autoexpand_vectornets_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitAutoexpand_vectornets_directive(this);
}

SV3_1aPpParser::Autoexpand_vectornets_directiveContext* SV3_1aPpParser::autoexpand_vectornets_directive() {
  Autoexpand_vectornets_directiveContext *_localctx = _tracker.createInstance<Autoexpand_vectornets_directiveContext>(_ctx, getState());
  enterRule(_localctx, 82, SV3_1aPpParser::RuleAutoexpand_vectornets_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(514);
    match(SV3_1aPpParser::TICK_AUTOEXPAND_VECTORNETS);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Uselib_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Uselib_directiveContext::Uselib_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Uselib_directiveContext::TICK_USELIB() {
  return getToken(SV3_1aPpParser::TICK_USELIB, 0);
}

std::vector<SV3_1aPpParser::Text_blobContext *> SV3_1aPpParser::Uselib_directiveContext::text_blob() {
  return getRuleContexts<SV3_1aPpParser::Text_blobContext>();
}

SV3_1aPpParser::Text_blobContext* SV3_1aPpParser::Uselib_directiveContext::text_blob(size_t i) {
  return getRuleContext<SV3_1aPpParser::Text_blobContext>(i);
}


size_t SV3_1aPpParser::Uselib_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleUselib_directive;
}

void SV3_1aPpParser::Uselib_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterUselib_directive(this);
}

void SV3_1aPpParser::Uselib_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitUselib_directive(this);
}

SV3_1aPpParser::Uselib_directiveContext* SV3_1aPpParser::uselib_directive() {
  Uselib_directiveContext *_localctx = _tracker.createInstance<Uselib_directiveContext>(_ctx, getState());
  enterRule(_localctx, 84, SV3_1aPpParser::RuleUselib_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    size_t alt;
    enterOuterAlt(_localctx, 1);
    setState(516);
    match(SV3_1aPpParser::TICK_USELIB);
    setState(518); 
    _errHandler->sync(this);
    alt = 1;
    do {
      switch (alt) {
        case 1: {
              setState(517);
              text_blob();
              break;
            }

      default:
        throw NoViableAltException(this);
      }
      setState(520); 
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 27, _ctx);
    } while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Disable_portfaults_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Disable_portfaults_directiveContext::Disable_portfaults_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Disable_portfaults_directiveContext::TICK_DISABLE_PORTFAULTS() {
  return getToken(SV3_1aPpParser::TICK_DISABLE_PORTFAULTS, 0);
}


size_t SV3_1aPpParser::Disable_portfaults_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleDisable_portfaults_directive;
}

void SV3_1aPpParser::Disable_portfaults_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterDisable_portfaults_directive(this);
}

void SV3_1aPpParser::Disable_portfaults_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitDisable_portfaults_directive(this);
}

SV3_1aPpParser::Disable_portfaults_directiveContext* SV3_1aPpParser::disable_portfaults_directive() {
  Disable_portfaults_directiveContext *_localctx = _tracker.createInstance<Disable_portfaults_directiveContext>(_ctx, getState());
  enterRule(_localctx, 86, SV3_1aPpParser::RuleDisable_portfaults_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(522);
    match(SV3_1aPpParser::TICK_DISABLE_PORTFAULTS);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Enable_portfaults_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Enable_portfaults_directiveContext::Enable_portfaults_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Enable_portfaults_directiveContext::TICK_ENABLE_PORTFAULTS() {
  return getToken(SV3_1aPpParser::TICK_ENABLE_PORTFAULTS, 0);
}


size_t SV3_1aPpParser::Enable_portfaults_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleEnable_portfaults_directive;
}

void SV3_1aPpParser::Enable_portfaults_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterEnable_portfaults_directive(this);
}

void SV3_1aPpParser::Enable_portfaults_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitEnable_portfaults_directive(this);
}

SV3_1aPpParser::Enable_portfaults_directiveContext* SV3_1aPpParser::enable_portfaults_directive() {
  Enable_portfaults_directiveContext *_localctx = _tracker.createInstance<Enable_portfaults_directiveContext>(_ctx, getState());
  enterRule(_localctx, 88, SV3_1aPpParser::RuleEnable_portfaults_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(524);
    match(SV3_1aPpParser::TICK_ENABLE_PORTFAULTS);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Nosuppress_faults_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Nosuppress_faults_directiveContext::Nosuppress_faults_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Nosuppress_faults_directiveContext::TICK_NOSUPPRESS_FAULTS() {
  return getToken(SV3_1aPpParser::TICK_NOSUPPRESS_FAULTS, 0);
}


size_t SV3_1aPpParser::Nosuppress_faults_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleNosuppress_faults_directive;
}

void SV3_1aPpParser::Nosuppress_faults_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterNosuppress_faults_directive(this);
}

void SV3_1aPpParser::Nosuppress_faults_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitNosuppress_faults_directive(this);
}

SV3_1aPpParser::Nosuppress_faults_directiveContext* SV3_1aPpParser::nosuppress_faults_directive() {
  Nosuppress_faults_directiveContext *_localctx = _tracker.createInstance<Nosuppress_faults_directiveContext>(_ctx, getState());
  enterRule(_localctx, 90, SV3_1aPpParser::RuleNosuppress_faults_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(526);
    match(SV3_1aPpParser::TICK_NOSUPPRESS_FAULTS);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Suppress_faults_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Suppress_faults_directiveContext::Suppress_faults_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Suppress_faults_directiveContext::TICK_SUPPRESS_FAULTS() {
  return getToken(SV3_1aPpParser::TICK_SUPPRESS_FAULTS, 0);
}


size_t SV3_1aPpParser::Suppress_faults_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleSuppress_faults_directive;
}

void SV3_1aPpParser::Suppress_faults_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterSuppress_faults_directive(this);
}

void SV3_1aPpParser::Suppress_faults_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitSuppress_faults_directive(this);
}

SV3_1aPpParser::Suppress_faults_directiveContext* SV3_1aPpParser::suppress_faults_directive() {
  Suppress_faults_directiveContext *_localctx = _tracker.createInstance<Suppress_faults_directiveContext>(_ctx, getState());
  enterRule(_localctx, 92, SV3_1aPpParser::RuleSuppress_faults_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(528);
    match(SV3_1aPpParser::TICK_SUPPRESS_FAULTS);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Signed_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Signed_directiveContext::Signed_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Signed_directiveContext::TICK_SIGNED() {
  return getToken(SV3_1aPpParser::TICK_SIGNED, 0);
}


size_t SV3_1aPpParser::Signed_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleSigned_directive;
}

void SV3_1aPpParser::Signed_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterSigned_directive(this);
}

void SV3_1aPpParser::Signed_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitSigned_directive(this);
}

SV3_1aPpParser::Signed_directiveContext* SV3_1aPpParser::signed_directive() {
  Signed_directiveContext *_localctx = _tracker.createInstance<Signed_directiveContext>(_ctx, getState());
  enterRule(_localctx, 94, SV3_1aPpParser::RuleSigned_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(530);
    match(SV3_1aPpParser::TICK_SIGNED);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Unsigned_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Unsigned_directiveContext::Unsigned_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Unsigned_directiveContext::TICK_UNSIGNED() {
  return getToken(SV3_1aPpParser::TICK_UNSIGNED, 0);
}


size_t SV3_1aPpParser::Unsigned_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleUnsigned_directive;
}

void SV3_1aPpParser::Unsigned_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterUnsigned_directive(this);
}

void SV3_1aPpParser::Unsigned_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitUnsigned_directive(this);
}

SV3_1aPpParser::Unsigned_directiveContext* SV3_1aPpParser::unsigned_directive() {
  Unsigned_directiveContext *_localctx = _tracker.createInstance<Unsigned_directiveContext>(_ctx, getState());
  enterRule(_localctx, 96, SV3_1aPpParser::RuleUnsigned_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(532);
    match(SV3_1aPpParser::TICK_UNSIGNED);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Remove_gatename_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Remove_gatename_directiveContext::Remove_gatename_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Remove_gatename_directiveContext::TICK_REMOVE_GATENAME() {
  return getToken(SV3_1aPpParser::TICK_REMOVE_GATENAME, 0);
}


size_t SV3_1aPpParser::Remove_gatename_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleRemove_gatename_directive;
}

void SV3_1aPpParser::Remove_gatename_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterRemove_gatename_directive(this);
}

void SV3_1aPpParser::Remove_gatename_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitRemove_gatename_directive(this);
}

SV3_1aPpParser::Remove_gatename_directiveContext* SV3_1aPpParser::remove_gatename_directive() {
  Remove_gatename_directiveContext *_localctx = _tracker.createInstance<Remove_gatename_directiveContext>(_ctx, getState());
  enterRule(_localctx, 98, SV3_1aPpParser::RuleRemove_gatename_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(534);
    match(SV3_1aPpParser::TICK_REMOVE_GATENAME);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Noremove_gatenames_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Noremove_gatenames_directiveContext::Noremove_gatenames_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Noremove_gatenames_directiveContext::TICK_NOREMOVE_GATENAMES() {
  return getToken(SV3_1aPpParser::TICK_NOREMOVE_GATENAMES, 0);
}


size_t SV3_1aPpParser::Noremove_gatenames_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleNoremove_gatenames_directive;
}

void SV3_1aPpParser::Noremove_gatenames_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterNoremove_gatenames_directive(this);
}

void SV3_1aPpParser::Noremove_gatenames_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitNoremove_gatenames_directive(this);
}

SV3_1aPpParser::Noremove_gatenames_directiveContext* SV3_1aPpParser::noremove_gatenames_directive() {
  Noremove_gatenames_directiveContext *_localctx = _tracker.createInstance<Noremove_gatenames_directiveContext>(_ctx, getState());
  enterRule(_localctx, 100, SV3_1aPpParser::RuleNoremove_gatenames_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(536);
    match(SV3_1aPpParser::TICK_NOREMOVE_GATENAMES);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Remove_netname_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Remove_netname_directiveContext::Remove_netname_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Remove_netname_directiveContext::TICK_REMOVE_NETNAME() {
  return getToken(SV3_1aPpParser::TICK_REMOVE_NETNAME, 0);
}


size_t SV3_1aPpParser::Remove_netname_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleRemove_netname_directive;
}

void SV3_1aPpParser::Remove_netname_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterRemove_netname_directive(this);
}

void SV3_1aPpParser::Remove_netname_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitRemove_netname_directive(this);
}

SV3_1aPpParser::Remove_netname_directiveContext* SV3_1aPpParser::remove_netname_directive() {
  Remove_netname_directiveContext *_localctx = _tracker.createInstance<Remove_netname_directiveContext>(_ctx, getState());
  enterRule(_localctx, 102, SV3_1aPpParser::RuleRemove_netname_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(538);
    match(SV3_1aPpParser::TICK_REMOVE_NETNAME);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Noremove_netnames_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Noremove_netnames_directiveContext::Noremove_netnames_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Noremove_netnames_directiveContext::TICK_NOREMOVE_NETNAMES() {
  return getToken(SV3_1aPpParser::TICK_NOREMOVE_NETNAMES, 0);
}


size_t SV3_1aPpParser::Noremove_netnames_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleNoremove_netnames_directive;
}

void SV3_1aPpParser::Noremove_netnames_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterNoremove_netnames_directive(this);
}

void SV3_1aPpParser::Noremove_netnames_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitNoremove_netnames_directive(this);
}

SV3_1aPpParser::Noremove_netnames_directiveContext* SV3_1aPpParser::noremove_netnames_directive() {
  Noremove_netnames_directiveContext *_localctx = _tracker.createInstance<Noremove_netnames_directiveContext>(_ctx, getState());
  enterRule(_localctx, 104, SV3_1aPpParser::RuleNoremove_netnames_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(540);
    match(SV3_1aPpParser::TICK_NOREMOVE_NETNAMES);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Accelerate_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Accelerate_directiveContext::Accelerate_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Accelerate_directiveContext::TICK_ACCELERATE() {
  return getToken(SV3_1aPpParser::TICK_ACCELERATE, 0);
}


size_t SV3_1aPpParser::Accelerate_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleAccelerate_directive;
}

void SV3_1aPpParser::Accelerate_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterAccelerate_directive(this);
}

void SV3_1aPpParser::Accelerate_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitAccelerate_directive(this);
}

SV3_1aPpParser::Accelerate_directiveContext* SV3_1aPpParser::accelerate_directive() {
  Accelerate_directiveContext *_localctx = _tracker.createInstance<Accelerate_directiveContext>(_ctx, getState());
  enterRule(_localctx, 106, SV3_1aPpParser::RuleAccelerate_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(542);
    match(SV3_1aPpParser::TICK_ACCELERATE);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Noaccelerate_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Noaccelerate_directiveContext::Noaccelerate_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Noaccelerate_directiveContext::TICK_NOACCELERATE() {
  return getToken(SV3_1aPpParser::TICK_NOACCELERATE, 0);
}


size_t SV3_1aPpParser::Noaccelerate_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleNoaccelerate_directive;
}

void SV3_1aPpParser::Noaccelerate_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterNoaccelerate_directive(this);
}

void SV3_1aPpParser::Noaccelerate_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitNoaccelerate_directive(this);
}

SV3_1aPpParser::Noaccelerate_directiveContext* SV3_1aPpParser::noaccelerate_directive() {
  Noaccelerate_directiveContext *_localctx = _tracker.createInstance<Noaccelerate_directiveContext>(_ctx, getState());
  enterRule(_localctx, 108, SV3_1aPpParser::RuleNoaccelerate_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(544);
    match(SV3_1aPpParser::TICK_NOACCELERATE);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Default_trireg_strenght_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Default_trireg_strenght_directiveContext::Default_trireg_strenght_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Default_trireg_strenght_directiveContext::TICK_DEFAULT_TRIREG_STRENGTH() {
  return getToken(SV3_1aPpParser::TICK_DEFAULT_TRIREG_STRENGTH, 0);
}

tree::TerminalNode* SV3_1aPpParser::Default_trireg_strenght_directiveContext::Spaces() {
  return getToken(SV3_1aPpParser::Spaces, 0);
}

SV3_1aPpParser::NumberContext* SV3_1aPpParser::Default_trireg_strenght_directiveContext::number() {
  return getRuleContext<SV3_1aPpParser::NumberContext>(0);
}


size_t SV3_1aPpParser::Default_trireg_strenght_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleDefault_trireg_strenght_directive;
}

void SV3_1aPpParser::Default_trireg_strenght_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterDefault_trireg_strenght_directive(this);
}

void SV3_1aPpParser::Default_trireg_strenght_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitDefault_trireg_strenght_directive(this);
}

SV3_1aPpParser::Default_trireg_strenght_directiveContext* SV3_1aPpParser::default_trireg_strenght_directive() {
  Default_trireg_strenght_directiveContext *_localctx = _tracker.createInstance<Default_trireg_strenght_directiveContext>(_ctx, getState());
  enterRule(_localctx, 110, SV3_1aPpParser::RuleDefault_trireg_strenght_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(546);
    match(SV3_1aPpParser::TICK_DEFAULT_TRIREG_STRENGTH);
    setState(547);
    match(SV3_1aPpParser::Spaces);
    setState(548);
    number();
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Default_decay_time_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Default_decay_time_directiveContext::Default_decay_time_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Default_decay_time_directiveContext::TICK_DEFAULT_DECAY_TIME() {
  return getToken(SV3_1aPpParser::TICK_DEFAULT_DECAY_TIME, 0);
}

tree::TerminalNode* SV3_1aPpParser::Default_decay_time_directiveContext::Spaces() {
  return getToken(SV3_1aPpParser::Spaces, 0);
}

SV3_1aPpParser::NumberContext* SV3_1aPpParser::Default_decay_time_directiveContext::number() {
  return getRuleContext<SV3_1aPpParser::NumberContext>(0);
}

tree::TerminalNode* SV3_1aPpParser::Default_decay_time_directiveContext::Simple_identifier() {
  return getToken(SV3_1aPpParser::Simple_identifier, 0);
}

tree::TerminalNode* SV3_1aPpParser::Default_decay_time_directiveContext::Fixed_point_number() {
  return getToken(SV3_1aPpParser::Fixed_point_number, 0);
}


size_t SV3_1aPpParser::Default_decay_time_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleDefault_decay_time_directive;
}

void SV3_1aPpParser::Default_decay_time_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterDefault_decay_time_directive(this);
}

void SV3_1aPpParser::Default_decay_time_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitDefault_decay_time_directive(this);
}

SV3_1aPpParser::Default_decay_time_directiveContext* SV3_1aPpParser::default_decay_time_directive() {
  Default_decay_time_directiveContext *_localctx = _tracker.createInstance<Default_decay_time_directiveContext>(_ctx, getState());
  enterRule(_localctx, 112, SV3_1aPpParser::RuleDefault_decay_time_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(550);
    match(SV3_1aPpParser::TICK_DEFAULT_DECAY_TIME);
    setState(551);
    match(SV3_1aPpParser::Spaces);
    setState(555);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case SV3_1aPpParser::Number: {
        setState(552);
        number();
        break;
      }

      case SV3_1aPpParser::Simple_identifier: {
        setState(553);
        match(SV3_1aPpParser::Simple_identifier);
        break;
      }

      case SV3_1aPpParser::Fixed_point_number: {
        setState(554);
        match(SV3_1aPpParser::Fixed_point_number);
        break;
      }

    default:
      throw NoViableAltException(this);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Unconnected_drive_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Unconnected_drive_directiveContext::Unconnected_drive_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Unconnected_drive_directiveContext::TICK_UNCONNECTED_DRIVE() {
  return getToken(SV3_1aPpParser::TICK_UNCONNECTED_DRIVE, 0);
}

tree::TerminalNode* SV3_1aPpParser::Unconnected_drive_directiveContext::Spaces() {
  return getToken(SV3_1aPpParser::Spaces, 0);
}

tree::TerminalNode* SV3_1aPpParser::Unconnected_drive_directiveContext::Simple_identifier() {
  return getToken(SV3_1aPpParser::Simple_identifier, 0);
}


size_t SV3_1aPpParser::Unconnected_drive_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleUnconnected_drive_directive;
}

void SV3_1aPpParser::Unconnected_drive_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterUnconnected_drive_directive(this);
}

void SV3_1aPpParser::Unconnected_drive_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitUnconnected_drive_directive(this);
}

SV3_1aPpParser::Unconnected_drive_directiveContext* SV3_1aPpParser::unconnected_drive_directive() {
  Unconnected_drive_directiveContext *_localctx = _tracker.createInstance<Unconnected_drive_directiveContext>(_ctx, getState());
  enterRule(_localctx, 114, SV3_1aPpParser::RuleUnconnected_drive_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(557);
    match(SV3_1aPpParser::TICK_UNCONNECTED_DRIVE);
    setState(558);
    match(SV3_1aPpParser::Spaces);
    setState(559);
    match(SV3_1aPpParser::Simple_identifier);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Nounconnected_drive_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Nounconnected_drive_directiveContext::Nounconnected_drive_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Nounconnected_drive_directiveContext::TICK_NOUNCONNECTED_DRIVE() {
  return getToken(SV3_1aPpParser::TICK_NOUNCONNECTED_DRIVE, 0);
}

tree::TerminalNode* SV3_1aPpParser::Nounconnected_drive_directiveContext::CR() {
  return getToken(SV3_1aPpParser::CR, 0);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Nounconnected_drive_directiveContext::Spaces() {
  return getTokens(SV3_1aPpParser::Spaces);
}

tree::TerminalNode* SV3_1aPpParser::Nounconnected_drive_directiveContext::Spaces(size_t i) {
  return getToken(SV3_1aPpParser::Spaces, i);
}


size_t SV3_1aPpParser::Nounconnected_drive_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleNounconnected_drive_directive;
}

void SV3_1aPpParser::Nounconnected_drive_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterNounconnected_drive_directive(this);
}

void SV3_1aPpParser::Nounconnected_drive_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitNounconnected_drive_directive(this);
}

SV3_1aPpParser::Nounconnected_drive_directiveContext* SV3_1aPpParser::nounconnected_drive_directive() {
  Nounconnected_drive_directiveContext *_localctx = _tracker.createInstance<Nounconnected_drive_directiveContext>(_ctx, getState());
  enterRule(_localctx, 116, SV3_1aPpParser::RuleNounconnected_drive_directive);
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(561);
    match(SV3_1aPpParser::TICK_NOUNCONNECTED_DRIVE);
    setState(565);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (_la == SV3_1aPpParser::Spaces) {
      setState(562);
      match(SV3_1aPpParser::Spaces);
      setState(567);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
    setState(568);
    match(SV3_1aPpParser::CR);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Delay_mode_distributed_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Delay_mode_distributed_directiveContext::Delay_mode_distributed_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Delay_mode_distributed_directiveContext::TICK_DELAY_MODE_DISTRIBUTED() {
  return getToken(SV3_1aPpParser::TICK_DELAY_MODE_DISTRIBUTED, 0);
}


size_t SV3_1aPpParser::Delay_mode_distributed_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleDelay_mode_distributed_directive;
}

void SV3_1aPpParser::Delay_mode_distributed_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterDelay_mode_distributed_directive(this);
}

void SV3_1aPpParser::Delay_mode_distributed_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitDelay_mode_distributed_directive(this);
}

SV3_1aPpParser::Delay_mode_distributed_directiveContext* SV3_1aPpParser::delay_mode_distributed_directive() {
  Delay_mode_distributed_directiveContext *_localctx = _tracker.createInstance<Delay_mode_distributed_directiveContext>(_ctx, getState());
  enterRule(_localctx, 118, SV3_1aPpParser::RuleDelay_mode_distributed_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(570);
    match(SV3_1aPpParser::TICK_DELAY_MODE_DISTRIBUTED);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Delay_mode_path_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Delay_mode_path_directiveContext::Delay_mode_path_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Delay_mode_path_directiveContext::TICK_DELAY_MODE_PATH() {
  return getToken(SV3_1aPpParser::TICK_DELAY_MODE_PATH, 0);
}


size_t SV3_1aPpParser::Delay_mode_path_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleDelay_mode_path_directive;
}

void SV3_1aPpParser::Delay_mode_path_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterDelay_mode_path_directive(this);
}

void SV3_1aPpParser::Delay_mode_path_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitDelay_mode_path_directive(this);
}

SV3_1aPpParser::Delay_mode_path_directiveContext* SV3_1aPpParser::delay_mode_path_directive() {
  Delay_mode_path_directiveContext *_localctx = _tracker.createInstance<Delay_mode_path_directiveContext>(_ctx, getState());
  enterRule(_localctx, 120, SV3_1aPpParser::RuleDelay_mode_path_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(572);
    match(SV3_1aPpParser::TICK_DELAY_MODE_PATH);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Delay_mode_unit_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Delay_mode_unit_directiveContext::Delay_mode_unit_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Delay_mode_unit_directiveContext::TICK_DELAY_MODE_UNIT() {
  return getToken(SV3_1aPpParser::TICK_DELAY_MODE_UNIT, 0);
}


size_t SV3_1aPpParser::Delay_mode_unit_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleDelay_mode_unit_directive;
}

void SV3_1aPpParser::Delay_mode_unit_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterDelay_mode_unit_directive(this);
}

void SV3_1aPpParser::Delay_mode_unit_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitDelay_mode_unit_directive(this);
}

SV3_1aPpParser::Delay_mode_unit_directiveContext* SV3_1aPpParser::delay_mode_unit_directive() {
  Delay_mode_unit_directiveContext *_localctx = _tracker.createInstance<Delay_mode_unit_directiveContext>(_ctx, getState());
  enterRule(_localctx, 122, SV3_1aPpParser::RuleDelay_mode_unit_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(574);
    match(SV3_1aPpParser::TICK_DELAY_MODE_UNIT);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Delay_mode_zero_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Delay_mode_zero_directiveContext::Delay_mode_zero_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Delay_mode_zero_directiveContext::TICK_DELAY_MODE_ZERO() {
  return getToken(SV3_1aPpParser::TICK_DELAY_MODE_ZERO, 0);
}


size_t SV3_1aPpParser::Delay_mode_zero_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleDelay_mode_zero_directive;
}

void SV3_1aPpParser::Delay_mode_zero_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterDelay_mode_zero_directive(this);
}

void SV3_1aPpParser::Delay_mode_zero_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitDelay_mode_zero_directive(this);
}

SV3_1aPpParser::Delay_mode_zero_directiveContext* SV3_1aPpParser::delay_mode_zero_directive() {
  Delay_mode_zero_directiveContext *_localctx = _tracker.createInstance<Delay_mode_zero_directiveContext>(_ctx, getState());
  enterRule(_localctx, 124, SV3_1aPpParser::RuleDelay_mode_zero_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(576);
    match(SV3_1aPpParser::TICK_DELAY_MODE_ZERO);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Undefineall_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Undefineall_directiveContext::Undefineall_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Undefineall_directiveContext::TICK_UNDEFINEALL() {
  return getToken(SV3_1aPpParser::TICK_UNDEFINEALL, 0);
}


size_t SV3_1aPpParser::Undefineall_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleUndefineall_directive;
}

void SV3_1aPpParser::Undefineall_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterUndefineall_directive(this);
}

void SV3_1aPpParser::Undefineall_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitUndefineall_directive(this);
}

SV3_1aPpParser::Undefineall_directiveContext* SV3_1aPpParser::undefineall_directive() {
  Undefineall_directiveContext *_localctx = _tracker.createInstance<Undefineall_directiveContext>(_ctx, getState());
  enterRule(_localctx, 126, SV3_1aPpParser::RuleUndefineall_directive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(578);
    match(SV3_1aPpParser::TICK_UNDEFINEALL);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- ModuleContext ------------------------------------------------------------------

SV3_1aPpParser::ModuleContext::ModuleContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::ModuleContext::MODULE() {
  return getToken(SV3_1aPpParser::MODULE, 0);
}


size_t SV3_1aPpParser::ModuleContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleModule;
}

void SV3_1aPpParser::ModuleContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterModule(this);
}

void SV3_1aPpParser::ModuleContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitModule(this);
}

SV3_1aPpParser::ModuleContext* SV3_1aPpParser::module() {
  ModuleContext *_localctx = _tracker.createInstance<ModuleContext>(_ctx, getState());
  enterRule(_localctx, 128, SV3_1aPpParser::RuleModule);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(580);
    match(SV3_1aPpParser::MODULE);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- EndmoduleContext ------------------------------------------------------------------

SV3_1aPpParser::EndmoduleContext::EndmoduleContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::EndmoduleContext::ENDMODULE() {
  return getToken(SV3_1aPpParser::ENDMODULE, 0);
}


size_t SV3_1aPpParser::EndmoduleContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleEndmodule;
}

void SV3_1aPpParser::EndmoduleContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterEndmodule(this);
}

void SV3_1aPpParser::EndmoduleContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitEndmodule(this);
}

SV3_1aPpParser::EndmoduleContext* SV3_1aPpParser::endmodule() {
  EndmoduleContext *_localctx = _tracker.createInstance<EndmoduleContext>(_ctx, getState());
  enterRule(_localctx, 130, SV3_1aPpParser::RuleEndmodule);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(582);
    match(SV3_1aPpParser::ENDMODULE);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Sv_interfaceContext ------------------------------------------------------------------

SV3_1aPpParser::Sv_interfaceContext::Sv_interfaceContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Sv_interfaceContext::INTERFACE() {
  return getToken(SV3_1aPpParser::INTERFACE, 0);
}


size_t SV3_1aPpParser::Sv_interfaceContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleSv_interface;
}

void SV3_1aPpParser::Sv_interfaceContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterSv_interface(this);
}

void SV3_1aPpParser::Sv_interfaceContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitSv_interface(this);
}

SV3_1aPpParser::Sv_interfaceContext* SV3_1aPpParser::sv_interface() {
  Sv_interfaceContext *_localctx = _tracker.createInstance<Sv_interfaceContext>(_ctx, getState());
  enterRule(_localctx, 132, SV3_1aPpParser::RuleSv_interface);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(584);
    match(SV3_1aPpParser::INTERFACE);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- EndinterfaceContext ------------------------------------------------------------------

SV3_1aPpParser::EndinterfaceContext::EndinterfaceContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::EndinterfaceContext::ENDINTERFACE() {
  return getToken(SV3_1aPpParser::ENDINTERFACE, 0);
}


size_t SV3_1aPpParser::EndinterfaceContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleEndinterface;
}

void SV3_1aPpParser::EndinterfaceContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterEndinterface(this);
}

void SV3_1aPpParser::EndinterfaceContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitEndinterface(this);
}

SV3_1aPpParser::EndinterfaceContext* SV3_1aPpParser::endinterface() {
  EndinterfaceContext *_localctx = _tracker.createInstance<EndinterfaceContext>(_ctx, getState());
  enterRule(_localctx, 134, SV3_1aPpParser::RuleEndinterface);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(586);
    match(SV3_1aPpParser::ENDINTERFACE);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- ProgramContext ------------------------------------------------------------------

SV3_1aPpParser::ProgramContext::ProgramContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::ProgramContext::PROGRAM() {
  return getToken(SV3_1aPpParser::PROGRAM, 0);
}


size_t SV3_1aPpParser::ProgramContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleProgram;
}

void SV3_1aPpParser::ProgramContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterProgram(this);
}

void SV3_1aPpParser::ProgramContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitProgram(this);
}

SV3_1aPpParser::ProgramContext* SV3_1aPpParser::program() {
  ProgramContext *_localctx = _tracker.createInstance<ProgramContext>(_ctx, getState());
  enterRule(_localctx, 136, SV3_1aPpParser::RuleProgram);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(588);
    match(SV3_1aPpParser::PROGRAM);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- EndprogramContext ------------------------------------------------------------------

SV3_1aPpParser::EndprogramContext::EndprogramContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::EndprogramContext::ENDPROGRAM() {
  return getToken(SV3_1aPpParser::ENDPROGRAM, 0);
}


size_t SV3_1aPpParser::EndprogramContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleEndprogram;
}

void SV3_1aPpParser::EndprogramContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterEndprogram(this);
}

void SV3_1aPpParser::EndprogramContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitEndprogram(this);
}

SV3_1aPpParser::EndprogramContext* SV3_1aPpParser::endprogram() {
  EndprogramContext *_localctx = _tracker.createInstance<EndprogramContext>(_ctx, getState());
  enterRule(_localctx, 138, SV3_1aPpParser::RuleEndprogram);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(590);
    match(SV3_1aPpParser::ENDPROGRAM);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- PrimitiveContext ------------------------------------------------------------------

SV3_1aPpParser::PrimitiveContext::PrimitiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::PrimitiveContext::PRIMITIVE() {
  return getToken(SV3_1aPpParser::PRIMITIVE, 0);
}


size_t SV3_1aPpParser::PrimitiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RulePrimitive;
}

void SV3_1aPpParser::PrimitiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterPrimitive(this);
}

void SV3_1aPpParser::PrimitiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitPrimitive(this);
}

SV3_1aPpParser::PrimitiveContext* SV3_1aPpParser::primitive() {
  PrimitiveContext *_localctx = _tracker.createInstance<PrimitiveContext>(_ctx, getState());
  enterRule(_localctx, 140, SV3_1aPpParser::RulePrimitive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(592);
    match(SV3_1aPpParser::PRIMITIVE);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- EndprimitiveContext ------------------------------------------------------------------

SV3_1aPpParser::EndprimitiveContext::EndprimitiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::EndprimitiveContext::ENDPRIMITIVE() {
  return getToken(SV3_1aPpParser::ENDPRIMITIVE, 0);
}


size_t SV3_1aPpParser::EndprimitiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleEndprimitive;
}

void SV3_1aPpParser::EndprimitiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterEndprimitive(this);
}

void SV3_1aPpParser::EndprimitiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitEndprimitive(this);
}

SV3_1aPpParser::EndprimitiveContext* SV3_1aPpParser::endprimitive() {
  EndprimitiveContext *_localctx = _tracker.createInstance<EndprimitiveContext>(_ctx, getState());
  enterRule(_localctx, 142, SV3_1aPpParser::RuleEndprimitive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(594);
    match(SV3_1aPpParser::ENDPRIMITIVE);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Sv_packageContext ------------------------------------------------------------------

SV3_1aPpParser::Sv_packageContext::Sv_packageContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Sv_packageContext::PACKAGE() {
  return getToken(SV3_1aPpParser::PACKAGE, 0);
}


size_t SV3_1aPpParser::Sv_packageContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleSv_package;
}

void SV3_1aPpParser::Sv_packageContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterSv_package(this);
}

void SV3_1aPpParser::Sv_packageContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitSv_package(this);
}

SV3_1aPpParser::Sv_packageContext* SV3_1aPpParser::sv_package() {
  Sv_packageContext *_localctx = _tracker.createInstance<Sv_packageContext>(_ctx, getState());
  enterRule(_localctx, 144, SV3_1aPpParser::RuleSv_package);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(596);
    match(SV3_1aPpParser::PACKAGE);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- EndpackageContext ------------------------------------------------------------------

SV3_1aPpParser::EndpackageContext::EndpackageContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::EndpackageContext::ENDPACKAGE() {
  return getToken(SV3_1aPpParser::ENDPACKAGE, 0);
}


size_t SV3_1aPpParser::EndpackageContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleEndpackage;
}

void SV3_1aPpParser::EndpackageContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterEndpackage(this);
}

void SV3_1aPpParser::EndpackageContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitEndpackage(this);
}

SV3_1aPpParser::EndpackageContext* SV3_1aPpParser::endpackage() {
  EndpackageContext *_localctx = _tracker.createInstance<EndpackageContext>(_ctx, getState());
  enterRule(_localctx, 146, SV3_1aPpParser::RuleEndpackage);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(598);
    match(SV3_1aPpParser::ENDPACKAGE);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- CheckerContext ------------------------------------------------------------------

SV3_1aPpParser::CheckerContext::CheckerContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::CheckerContext::CHECKER() {
  return getToken(SV3_1aPpParser::CHECKER, 0);
}


size_t SV3_1aPpParser::CheckerContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleChecker;
}

void SV3_1aPpParser::CheckerContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterChecker(this);
}

void SV3_1aPpParser::CheckerContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitChecker(this);
}

SV3_1aPpParser::CheckerContext* SV3_1aPpParser::checker() {
  CheckerContext *_localctx = _tracker.createInstance<CheckerContext>(_ctx, getState());
  enterRule(_localctx, 148, SV3_1aPpParser::RuleChecker);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(600);
    match(SV3_1aPpParser::CHECKER);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- EndcheckerContext ------------------------------------------------------------------

SV3_1aPpParser::EndcheckerContext::EndcheckerContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::EndcheckerContext::ENDCHECKER() {
  return getToken(SV3_1aPpParser::ENDCHECKER, 0);
}


size_t SV3_1aPpParser::EndcheckerContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleEndchecker;
}

void SV3_1aPpParser::EndcheckerContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterEndchecker(this);
}

void SV3_1aPpParser::EndcheckerContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitEndchecker(this);
}

SV3_1aPpParser::EndcheckerContext* SV3_1aPpParser::endchecker() {
  EndcheckerContext *_localctx = _tracker.createInstance<EndcheckerContext>(_ctx, getState());
  enterRule(_localctx, 150, SV3_1aPpParser::RuleEndchecker);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(602);
    match(SV3_1aPpParser::ENDCHECKER);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- ConfigContext ------------------------------------------------------------------

SV3_1aPpParser::ConfigContext::ConfigContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::ConfigContext::CONFIG() {
  return getToken(SV3_1aPpParser::CONFIG, 0);
}


size_t SV3_1aPpParser::ConfigContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleConfig;
}

void SV3_1aPpParser::ConfigContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterConfig(this);
}

void SV3_1aPpParser::ConfigContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitConfig(this);
}

SV3_1aPpParser::ConfigContext* SV3_1aPpParser::config() {
  ConfigContext *_localctx = _tracker.createInstance<ConfigContext>(_ctx, getState());
  enterRule(_localctx, 152, SV3_1aPpParser::RuleConfig);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(604);
    match(SV3_1aPpParser::CONFIG);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- EndconfigContext ------------------------------------------------------------------

SV3_1aPpParser::EndconfigContext::EndconfigContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::EndconfigContext::ENDCONFIG() {
  return getToken(SV3_1aPpParser::ENDCONFIG, 0);
}


size_t SV3_1aPpParser::EndconfigContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleEndconfig;
}

void SV3_1aPpParser::EndconfigContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterEndconfig(this);
}

void SV3_1aPpParser::EndconfigContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitEndconfig(this);
}

SV3_1aPpParser::EndconfigContext* SV3_1aPpParser::endconfig() {
  EndconfigContext *_localctx = _tracker.createInstance<EndconfigContext>(_ctx, getState());
  enterRule(_localctx, 154, SV3_1aPpParser::RuleEndconfig);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(606);
    match(SV3_1aPpParser::ENDCONFIG);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Define_directiveContext ------------------------------------------------------------------

SV3_1aPpParser::Define_directiveContext::Define_directiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Define_directiveContext::TICK_DEFINE() {
  return getToken(SV3_1aPpParser::TICK_DEFINE, 0);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Define_directiveContext::Spaces() {
  return getTokens(SV3_1aPpParser::Spaces);
}

tree::TerminalNode* SV3_1aPpParser::Define_directiveContext::Spaces(size_t i) {
  return getToken(SV3_1aPpParser::Spaces, i);
}

tree::TerminalNode* SV3_1aPpParser::Define_directiveContext::CR() {
  return getToken(SV3_1aPpParser::CR, 0);
}

tree::TerminalNode* SV3_1aPpParser::Define_directiveContext::Simple_identifier() {
  return getToken(SV3_1aPpParser::Simple_identifier, 0);
}

tree::TerminalNode* SV3_1aPpParser::Define_directiveContext::Escaped_identifier() {
  return getToken(SV3_1aPpParser::Escaped_identifier, 0);
}


size_t SV3_1aPpParser::Define_directiveContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleDefine_directive;
}

void SV3_1aPpParser::Define_directiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterDefine_directive(this);
}

void SV3_1aPpParser::Define_directiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitDefine_directive(this);
}

SV3_1aPpParser::Define_directiveContext* SV3_1aPpParser::define_directive() {
  Define_directiveContext *_localctx = _tracker.createInstance<Define_directiveContext>(_ctx, getState());
  enterRule(_localctx, 156, SV3_1aPpParser::RuleDefine_directive);
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(608);
    match(SV3_1aPpParser::TICK_DEFINE);
    setState(609);
    match(SV3_1aPpParser::Spaces);
    setState(610);
    _la = _input->LA(1);
    if (!(_la == SV3_1aPpParser::Simple_identifier

    || _la == SV3_1aPpParser::Escaped_identifier)) {
    _errHandler->recoverInline(this);
    }
    else {
      _errHandler->reportMatch(this);
      consume();
    }
    setState(614);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (_la == SV3_1aPpParser::Spaces) {
      setState(611);
      match(SV3_1aPpParser::Spaces);
      setState(616);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
    setState(617);
    match(SV3_1aPpParser::CR);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Multiline_no_args_macro_definitionContext ------------------------------------------------------------------

SV3_1aPpParser::Multiline_no_args_macro_definitionContext::Multiline_no_args_macro_definitionContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Multiline_no_args_macro_definitionContext::TICK_DEFINE() {
  return getToken(SV3_1aPpParser::TICK_DEFINE, 0);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Multiline_no_args_macro_definitionContext::Spaces() {
  return getTokens(SV3_1aPpParser::Spaces);
}

tree::TerminalNode* SV3_1aPpParser::Multiline_no_args_macro_definitionContext::Spaces(size_t i) {
  return getToken(SV3_1aPpParser::Spaces, i);
}

SV3_1aPpParser::Escaped_macro_definition_bodyContext* SV3_1aPpParser::Multiline_no_args_macro_definitionContext::escaped_macro_definition_body() {
  return getRuleContext<SV3_1aPpParser::Escaped_macro_definition_bodyContext>(0);
}

tree::TerminalNode* SV3_1aPpParser::Multiline_no_args_macro_definitionContext::Simple_identifier() {
  return getToken(SV3_1aPpParser::Simple_identifier, 0);
}

tree::TerminalNode* SV3_1aPpParser::Multiline_no_args_macro_definitionContext::Escaped_identifier() {
  return getToken(SV3_1aPpParser::Escaped_identifier, 0);
}


size_t SV3_1aPpParser::Multiline_no_args_macro_definitionContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleMultiline_no_args_macro_definition;
}

void SV3_1aPpParser::Multiline_no_args_macro_definitionContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterMultiline_no_args_macro_definition(this);
}

void SV3_1aPpParser::Multiline_no_args_macro_definitionContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitMultiline_no_args_macro_definition(this);
}

SV3_1aPpParser::Multiline_no_args_macro_definitionContext* SV3_1aPpParser::multiline_no_args_macro_definition() {
  Multiline_no_args_macro_definitionContext *_localctx = _tracker.createInstance<Multiline_no_args_macro_definitionContext>(_ctx, getState());
  enterRule(_localctx, 158, SV3_1aPpParser::RuleMultiline_no_args_macro_definition);
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    size_t alt;
    enterOuterAlt(_localctx, 1);
    setState(619);
    match(SV3_1aPpParser::TICK_DEFINE);
    setState(620);
    match(SV3_1aPpParser::Spaces);
    setState(621);
    _la = _input->LA(1);
    if (!(_la == SV3_1aPpParser::Simple_identifier

    || _la == SV3_1aPpParser::Escaped_identifier)) {
    _errHandler->recoverInline(this);
    }
    else {
      _errHandler->reportMatch(this);
      consume();
    }
    setState(625);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 31, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        setState(622);
        match(SV3_1aPpParser::Spaces); 
      }
      setState(627);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 31, _ctx);
    }
    setState(628);
    escaped_macro_definition_body();
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Multiline_args_macro_definitionContext ------------------------------------------------------------------

SV3_1aPpParser::Multiline_args_macro_definitionContext::Multiline_args_macro_definitionContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Multiline_args_macro_definitionContext::TICK_DEFINE() {
  return getToken(SV3_1aPpParser::TICK_DEFINE, 0);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Multiline_args_macro_definitionContext::Spaces() {
  return getTokens(SV3_1aPpParser::Spaces);
}

tree::TerminalNode* SV3_1aPpParser::Multiline_args_macro_definitionContext::Spaces(size_t i) {
  return getToken(SV3_1aPpParser::Spaces, i);
}

SV3_1aPpParser::Macro_argumentsContext* SV3_1aPpParser::Multiline_args_macro_definitionContext::macro_arguments() {
  return getRuleContext<SV3_1aPpParser::Macro_argumentsContext>(0);
}

SV3_1aPpParser::Escaped_macro_definition_bodyContext* SV3_1aPpParser::Multiline_args_macro_definitionContext::escaped_macro_definition_body() {
  return getRuleContext<SV3_1aPpParser::Escaped_macro_definition_bodyContext>(0);
}

tree::TerminalNode* SV3_1aPpParser::Multiline_args_macro_definitionContext::Simple_identifier() {
  return getToken(SV3_1aPpParser::Simple_identifier, 0);
}

tree::TerminalNode* SV3_1aPpParser::Multiline_args_macro_definitionContext::Escaped_identifier() {
  return getToken(SV3_1aPpParser::Escaped_identifier, 0);
}


size_t SV3_1aPpParser::Multiline_args_macro_definitionContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleMultiline_args_macro_definition;
}

void SV3_1aPpParser::Multiline_args_macro_definitionContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterMultiline_args_macro_definition(this);
}

void SV3_1aPpParser::Multiline_args_macro_definitionContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitMultiline_args_macro_definition(this);
}

SV3_1aPpParser::Multiline_args_macro_definitionContext* SV3_1aPpParser::multiline_args_macro_definition() {
  Multiline_args_macro_definitionContext *_localctx = _tracker.createInstance<Multiline_args_macro_definitionContext>(_ctx, getState());
  enterRule(_localctx, 160, SV3_1aPpParser::RuleMultiline_args_macro_definition);
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    size_t alt;
    enterOuterAlt(_localctx, 1);
    setState(630);
    match(SV3_1aPpParser::TICK_DEFINE);
    setState(631);
    match(SV3_1aPpParser::Spaces);
    setState(632);
    _la = _input->LA(1);
    if (!(_la == SV3_1aPpParser::Simple_identifier

    || _la == SV3_1aPpParser::Escaped_identifier)) {
    _errHandler->recoverInline(this);
    }
    else {
      _errHandler->reportMatch(this);
      consume();
    }
    setState(633);
    macro_arguments();
    setState(637);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 32, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        setState(634);
        match(SV3_1aPpParser::Spaces); 
      }
      setState(639);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 32, _ctx);
    }
    setState(640);
    escaped_macro_definition_body();
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Simple_no_args_macro_definitionContext ------------------------------------------------------------------

SV3_1aPpParser::Simple_no_args_macro_definitionContext::Simple_no_args_macro_definitionContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Simple_no_args_macro_definitionContext::TICK_DEFINE() {
  return getToken(SV3_1aPpParser::TICK_DEFINE, 0);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_no_args_macro_definitionContext::Spaces() {
  return getTokens(SV3_1aPpParser::Spaces);
}

tree::TerminalNode* SV3_1aPpParser::Simple_no_args_macro_definitionContext::Spaces(size_t i) {
  return getToken(SV3_1aPpParser::Spaces, i);
}

SV3_1aPpParser::Simple_macro_definition_bodyContext* SV3_1aPpParser::Simple_no_args_macro_definitionContext::simple_macro_definition_body() {
  return getRuleContext<SV3_1aPpParser::Simple_macro_definition_bodyContext>(0);
}

tree::TerminalNode* SV3_1aPpParser::Simple_no_args_macro_definitionContext::Simple_identifier() {
  return getToken(SV3_1aPpParser::Simple_identifier, 0);
}

tree::TerminalNode* SV3_1aPpParser::Simple_no_args_macro_definitionContext::Escaped_identifier() {
  return getToken(SV3_1aPpParser::Escaped_identifier, 0);
}

tree::TerminalNode* SV3_1aPpParser::Simple_no_args_macro_definitionContext::CR() {
  return getToken(SV3_1aPpParser::CR, 0);
}

tree::TerminalNode* SV3_1aPpParser::Simple_no_args_macro_definitionContext::One_line_comment() {
  return getToken(SV3_1aPpParser::One_line_comment, 0);
}


size_t SV3_1aPpParser::Simple_no_args_macro_definitionContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleSimple_no_args_macro_definition;
}

void SV3_1aPpParser::Simple_no_args_macro_definitionContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterSimple_no_args_macro_definition(this);
}

void SV3_1aPpParser::Simple_no_args_macro_definitionContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitSimple_no_args_macro_definition(this);
}

SV3_1aPpParser::Simple_no_args_macro_definitionContext* SV3_1aPpParser::simple_no_args_macro_definition() {
  Simple_no_args_macro_definitionContext *_localctx = _tracker.createInstance<Simple_no_args_macro_definitionContext>(_ctx, getState());
  enterRule(_localctx, 162, SV3_1aPpParser::RuleSimple_no_args_macro_definition);
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    setState(659);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 34, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(642);
      match(SV3_1aPpParser::TICK_DEFINE);
      setState(643);
      match(SV3_1aPpParser::Spaces);
      setState(644);
      _la = _input->LA(1);
      if (!(_la == SV3_1aPpParser::Simple_identifier

      || _la == SV3_1aPpParser::Escaped_identifier)) {
      _errHandler->recoverInline(this);
      }
      else {
        _errHandler->reportMatch(this);
        consume();
      }
      setState(645);
      match(SV3_1aPpParser::Spaces);
      setState(646);
      simple_macro_definition_body();
      setState(647);
      _la = _input->LA(1);
      if (!(_la == SV3_1aPpParser::One_line_comment || _la == SV3_1aPpParser::CR)) {
      _errHandler->recoverInline(this);
      }
      else {
        _errHandler->reportMatch(this);
        consume();
      }
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(649);
      match(SV3_1aPpParser::TICK_DEFINE);
      setState(650);
      match(SV3_1aPpParser::Spaces);
      setState(651);
      _la = _input->LA(1);
      if (!(_la == SV3_1aPpParser::Simple_identifier

      || _la == SV3_1aPpParser::Escaped_identifier)) {
      _errHandler->recoverInline(this);
      }
      else {
        _errHandler->reportMatch(this);
        consume();
      }
      setState(655);
      _errHandler->sync(this);
      _la = _input->LA(1);
      while (_la == SV3_1aPpParser::Spaces) {
        setState(652);
        match(SV3_1aPpParser::Spaces);
        setState(657);
        _errHandler->sync(this);
        _la = _input->LA(1);
      }
      setState(658);
      match(SV3_1aPpParser::CR);
      break;
    }

    default:
      break;
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Simple_args_macro_definitionContext ------------------------------------------------------------------

SV3_1aPpParser::Simple_args_macro_definitionContext::Simple_args_macro_definitionContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Simple_args_macro_definitionContext::TICK_DEFINE() {
  return getToken(SV3_1aPpParser::TICK_DEFINE, 0);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_args_macro_definitionContext::Spaces() {
  return getTokens(SV3_1aPpParser::Spaces);
}

tree::TerminalNode* SV3_1aPpParser::Simple_args_macro_definitionContext::Spaces(size_t i) {
  return getToken(SV3_1aPpParser::Spaces, i);
}

SV3_1aPpParser::Macro_argumentsContext* SV3_1aPpParser::Simple_args_macro_definitionContext::macro_arguments() {
  return getRuleContext<SV3_1aPpParser::Macro_argumentsContext>(0);
}

SV3_1aPpParser::Simple_macro_definition_bodyContext* SV3_1aPpParser::Simple_args_macro_definitionContext::simple_macro_definition_body() {
  return getRuleContext<SV3_1aPpParser::Simple_macro_definition_bodyContext>(0);
}

tree::TerminalNode* SV3_1aPpParser::Simple_args_macro_definitionContext::Simple_identifier() {
  return getToken(SV3_1aPpParser::Simple_identifier, 0);
}

tree::TerminalNode* SV3_1aPpParser::Simple_args_macro_definitionContext::Escaped_identifier() {
  return getToken(SV3_1aPpParser::Escaped_identifier, 0);
}

tree::TerminalNode* SV3_1aPpParser::Simple_args_macro_definitionContext::CR() {
  return getToken(SV3_1aPpParser::CR, 0);
}

tree::TerminalNode* SV3_1aPpParser::Simple_args_macro_definitionContext::One_line_comment() {
  return getToken(SV3_1aPpParser::One_line_comment, 0);
}


size_t SV3_1aPpParser::Simple_args_macro_definitionContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleSimple_args_macro_definition;
}

void SV3_1aPpParser::Simple_args_macro_definitionContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterSimple_args_macro_definition(this);
}

void SV3_1aPpParser::Simple_args_macro_definitionContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitSimple_args_macro_definition(this);
}

SV3_1aPpParser::Simple_args_macro_definitionContext* SV3_1aPpParser::simple_args_macro_definition() {
  Simple_args_macro_definitionContext *_localctx = _tracker.createInstance<Simple_args_macro_definitionContext>(_ctx, getState());
  enterRule(_localctx, 164, SV3_1aPpParser::RuleSimple_args_macro_definition);
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    setState(681);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 36, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(661);
      match(SV3_1aPpParser::TICK_DEFINE);
      setState(662);
      match(SV3_1aPpParser::Spaces);
      setState(663);
      _la = _input->LA(1);
      if (!(_la == SV3_1aPpParser::Simple_identifier

      || _la == SV3_1aPpParser::Escaped_identifier)) {
      _errHandler->recoverInline(this);
      }
      else {
        _errHandler->reportMatch(this);
        consume();
      }
      setState(664);
      macro_arguments();
      setState(665);
      match(SV3_1aPpParser::Spaces);
      setState(666);
      simple_macro_definition_body();
      setState(667);
      _la = _input->LA(1);
      if (!(_la == SV3_1aPpParser::One_line_comment || _la == SV3_1aPpParser::CR)) {
      _errHandler->recoverInline(this);
      }
      else {
        _errHandler->reportMatch(this);
        consume();
      }
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(669);
      match(SV3_1aPpParser::TICK_DEFINE);
      setState(670);
      match(SV3_1aPpParser::Spaces);
      setState(671);
      _la = _input->LA(1);
      if (!(_la == SV3_1aPpParser::Simple_identifier

      || _la == SV3_1aPpParser::Escaped_identifier)) {
      _errHandler->recoverInline(this);
      }
      else {
        _errHandler->reportMatch(this);
        consume();
      }
      setState(672);
      macro_arguments();
      setState(676);
      _errHandler->sync(this);
      _la = _input->LA(1);
      while (_la == SV3_1aPpParser::Spaces) {
        setState(673);
        match(SV3_1aPpParser::Spaces);
        setState(678);
        _errHandler->sync(this);
        _la = _input->LA(1);
      }
      setState(679);
      match(SV3_1aPpParser::CR);
      break;
    }

    default:
      break;
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Identifier_in_macro_bodyContext ------------------------------------------------------------------

SV3_1aPpParser::Identifier_in_macro_bodyContext::Identifier_in_macro_bodyContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Identifier_in_macro_bodyContext::Simple_identifier() {
  return getTokens(SV3_1aPpParser::Simple_identifier);
}

tree::TerminalNode* SV3_1aPpParser::Identifier_in_macro_bodyContext::Simple_identifier(size_t i) {
  return getToken(SV3_1aPpParser::Simple_identifier, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Identifier_in_macro_bodyContext::TICK_TICK() {
  return getTokens(SV3_1aPpParser::TICK_TICK);
}

tree::TerminalNode* SV3_1aPpParser::Identifier_in_macro_bodyContext::TICK_TICK(size_t i) {
  return getToken(SV3_1aPpParser::TICK_TICK, i);
}


size_t SV3_1aPpParser::Identifier_in_macro_bodyContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleIdentifier_in_macro_body;
}

void SV3_1aPpParser::Identifier_in_macro_bodyContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterIdentifier_in_macro_body(this);
}

void SV3_1aPpParser::Identifier_in_macro_bodyContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitIdentifier_in_macro_body(this);
}

SV3_1aPpParser::Identifier_in_macro_bodyContext* SV3_1aPpParser::identifier_in_macro_body() {
  Identifier_in_macro_bodyContext *_localctx = _tracker.createInstance<Identifier_in_macro_bodyContext>(_ctx, getState());
  enterRule(_localctx, 166, SV3_1aPpParser::RuleIdentifier_in_macro_body);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    size_t alt;
    enterOuterAlt(_localctx, 1);
    setState(689);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 38, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        setState(683);
        match(SV3_1aPpParser::Simple_identifier);
        setState(685);
        _errHandler->sync(this);

        switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 37, _ctx)) {
        case 1: {
          setState(684);
          match(SV3_1aPpParser::TICK_TICK);
          break;
        }

        default:
          break;
        } 
      }
      setState(691);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 38, _ctx);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Simple_no_args_macro_definition_in_macro_bodyContext ------------------------------------------------------------------

SV3_1aPpParser::Simple_no_args_macro_definition_in_macro_bodyContext::Simple_no_args_macro_definition_in_macro_bodyContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Simple_no_args_macro_definition_in_macro_bodyContext::TICK_DEFINE() {
  return getToken(SV3_1aPpParser::TICK_DEFINE, 0);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_no_args_macro_definition_in_macro_bodyContext::Spaces() {
  return getTokens(SV3_1aPpParser::Spaces);
}

tree::TerminalNode* SV3_1aPpParser::Simple_no_args_macro_definition_in_macro_bodyContext::Spaces(size_t i) {
  return getToken(SV3_1aPpParser::Spaces, i);
}

SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext* SV3_1aPpParser::Simple_no_args_macro_definition_in_macro_bodyContext::simple_macro_definition_body_in_macro_body() {
  return getRuleContext<SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext>(0);
}

SV3_1aPpParser::Identifier_in_macro_bodyContext* SV3_1aPpParser::Simple_no_args_macro_definition_in_macro_bodyContext::identifier_in_macro_body() {
  return getRuleContext<SV3_1aPpParser::Identifier_in_macro_bodyContext>(0);
}

tree::TerminalNode* SV3_1aPpParser::Simple_no_args_macro_definition_in_macro_bodyContext::Escaped_identifier() {
  return getToken(SV3_1aPpParser::Escaped_identifier, 0);
}

tree::TerminalNode* SV3_1aPpParser::Simple_no_args_macro_definition_in_macro_bodyContext::TICK_VARIABLE() {
  return getToken(SV3_1aPpParser::TICK_VARIABLE, 0);
}


size_t SV3_1aPpParser::Simple_no_args_macro_definition_in_macro_bodyContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleSimple_no_args_macro_definition_in_macro_body;
}

void SV3_1aPpParser::Simple_no_args_macro_definition_in_macro_bodyContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterSimple_no_args_macro_definition_in_macro_body(this);
}

void SV3_1aPpParser::Simple_no_args_macro_definition_in_macro_bodyContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitSimple_no_args_macro_definition_in_macro_body(this);
}

SV3_1aPpParser::Simple_no_args_macro_definition_in_macro_bodyContext* SV3_1aPpParser::simple_no_args_macro_definition_in_macro_body() {
  Simple_no_args_macro_definition_in_macro_bodyContext *_localctx = _tracker.createInstance<Simple_no_args_macro_definition_in_macro_bodyContext>(_ctx, getState());
  enterRule(_localctx, 168, SV3_1aPpParser::RuleSimple_no_args_macro_definition_in_macro_body);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    size_t alt;
    setState(720);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 43, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(692);
      match(SV3_1aPpParser::TICK_DEFINE);
      setState(693);
      match(SV3_1aPpParser::Spaces);
      setState(696);
      _errHandler->sync(this);
      switch (_input->LA(1)) {
        case SV3_1aPpParser::Simple_identifier:
        case SV3_1aPpParser::Spaces: {
          setState(694);
          identifier_in_macro_body();
          break;
        }

        case SV3_1aPpParser::Escaped_identifier: {
          setState(695);
          match(SV3_1aPpParser::Escaped_identifier);
          break;
        }

      default:
        throw NoViableAltException(this);
      }
      setState(698);
      match(SV3_1aPpParser::Spaces);
      setState(699);
      simple_macro_definition_body_in_macro_body();
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(700);
      match(SV3_1aPpParser::TICK_DEFINE);
      setState(701);
      match(SV3_1aPpParser::Spaces);
      setState(704);
      _errHandler->sync(this);
      switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 40, _ctx)) {
      case 1: {
        setState(702);
        identifier_in_macro_body();
        break;
      }

      case 2: {
        setState(703);
        match(SV3_1aPpParser::Escaped_identifier);
        break;
      }

      default:
        break;
      }
      setState(709);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 41, _ctx);
      while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
        if (alt == 1) {
          setState(706);
          match(SV3_1aPpParser::Spaces); 
        }
        setState(711);
        _errHandler->sync(this);
        alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 41, _ctx);
      }
      break;
    }

    case 3: {
      enterOuterAlt(_localctx, 3);
      setState(712);
      match(SV3_1aPpParser::TICK_DEFINE);
      setState(713);
      match(SV3_1aPpParser::Spaces);
      setState(716);
      _errHandler->sync(this);
      switch (_input->LA(1)) {
        case SV3_1aPpParser::TICK_VARIABLE:
        case SV3_1aPpParser::Simple_identifier: {
          setState(714);
          identifier_in_macro_body();
          break;
        }

        case SV3_1aPpParser::Escaped_identifier: {
          setState(715);
          match(SV3_1aPpParser::Escaped_identifier);
          break;
        }

      default:
        throw NoViableAltException(this);
      }
      setState(718);
      match(SV3_1aPpParser::TICK_VARIABLE);
      setState(719);
      simple_macro_definition_body_in_macro_body();
      break;
    }

    default:
      break;
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Simple_args_macro_definition_in_macro_bodyContext ------------------------------------------------------------------

SV3_1aPpParser::Simple_args_macro_definition_in_macro_bodyContext::Simple_args_macro_definition_in_macro_bodyContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Simple_args_macro_definition_in_macro_bodyContext::TICK_DEFINE() {
  return getToken(SV3_1aPpParser::TICK_DEFINE, 0);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_args_macro_definition_in_macro_bodyContext::Spaces() {
  return getTokens(SV3_1aPpParser::Spaces);
}

tree::TerminalNode* SV3_1aPpParser::Simple_args_macro_definition_in_macro_bodyContext::Spaces(size_t i) {
  return getToken(SV3_1aPpParser::Spaces, i);
}

SV3_1aPpParser::Macro_argumentsContext* SV3_1aPpParser::Simple_args_macro_definition_in_macro_bodyContext::macro_arguments() {
  return getRuleContext<SV3_1aPpParser::Macro_argumentsContext>(0);
}

SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext* SV3_1aPpParser::Simple_args_macro_definition_in_macro_bodyContext::simple_macro_definition_body_in_macro_body() {
  return getRuleContext<SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext>(0);
}

SV3_1aPpParser::Identifier_in_macro_bodyContext* SV3_1aPpParser::Simple_args_macro_definition_in_macro_bodyContext::identifier_in_macro_body() {
  return getRuleContext<SV3_1aPpParser::Identifier_in_macro_bodyContext>(0);
}

tree::TerminalNode* SV3_1aPpParser::Simple_args_macro_definition_in_macro_bodyContext::Escaped_identifier() {
  return getToken(SV3_1aPpParser::Escaped_identifier, 0);
}


size_t SV3_1aPpParser::Simple_args_macro_definition_in_macro_bodyContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleSimple_args_macro_definition_in_macro_body;
}

void SV3_1aPpParser::Simple_args_macro_definition_in_macro_bodyContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterSimple_args_macro_definition_in_macro_body(this);
}

void SV3_1aPpParser::Simple_args_macro_definition_in_macro_bodyContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitSimple_args_macro_definition_in_macro_body(this);
}

SV3_1aPpParser::Simple_args_macro_definition_in_macro_bodyContext* SV3_1aPpParser::simple_args_macro_definition_in_macro_body() {
  Simple_args_macro_definition_in_macro_bodyContext *_localctx = _tracker.createInstance<Simple_args_macro_definition_in_macro_bodyContext>(_ctx, getState());
  enterRule(_localctx, 170, SV3_1aPpParser::RuleSimple_args_macro_definition_in_macro_body);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    setState(739);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 46, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(722);
      match(SV3_1aPpParser::TICK_DEFINE);
      setState(723);
      match(SV3_1aPpParser::Spaces);
      setState(726);
      _errHandler->sync(this);
      switch (_input->LA(1)) {
        case SV3_1aPpParser::Simple_identifier:
        case SV3_1aPpParser::PARENS_OPEN: {
          setState(724);
          identifier_in_macro_body();
          break;
        }

        case SV3_1aPpParser::Escaped_identifier: {
          setState(725);
          match(SV3_1aPpParser::Escaped_identifier);
          break;
        }

      default:
        throw NoViableAltException(this);
      }
      setState(728);
      macro_arguments();
      setState(729);
      match(SV3_1aPpParser::Spaces);
      setState(730);
      simple_macro_definition_body_in_macro_body();
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(732);
      match(SV3_1aPpParser::TICK_DEFINE);
      setState(733);
      match(SV3_1aPpParser::Spaces);
      setState(736);
      _errHandler->sync(this);
      switch (_input->LA(1)) {
        case SV3_1aPpParser::Simple_identifier:
        case SV3_1aPpParser::PARENS_OPEN: {
          setState(734);
          identifier_in_macro_body();
          break;
        }

        case SV3_1aPpParser::Escaped_identifier: {
          setState(735);
          match(SV3_1aPpParser::Escaped_identifier);
          break;
        }

      default:
        throw NoViableAltException(this);
      }
      setState(738);
      macro_arguments();
      break;
    }

    default:
      break;
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Directive_in_macroContext ------------------------------------------------------------------

SV3_1aPpParser::Directive_in_macroContext::Directive_in_macroContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

SV3_1aPpParser::Celldefine_directiveContext* SV3_1aPpParser::Directive_in_macroContext::celldefine_directive() {
  return getRuleContext<SV3_1aPpParser::Celldefine_directiveContext>(0);
}

SV3_1aPpParser::Endcelldefine_directiveContext* SV3_1aPpParser::Directive_in_macroContext::endcelldefine_directive() {
  return getRuleContext<SV3_1aPpParser::Endcelldefine_directiveContext>(0);
}

SV3_1aPpParser::Default_nettype_directiveContext* SV3_1aPpParser::Directive_in_macroContext::default_nettype_directive() {
  return getRuleContext<SV3_1aPpParser::Default_nettype_directiveContext>(0);
}

SV3_1aPpParser::Undef_directiveContext* SV3_1aPpParser::Directive_in_macroContext::undef_directive() {
  return getRuleContext<SV3_1aPpParser::Undef_directiveContext>(0);
}

SV3_1aPpParser::Ifdef_directiveContext* SV3_1aPpParser::Directive_in_macroContext::ifdef_directive() {
  return getRuleContext<SV3_1aPpParser::Ifdef_directiveContext>(0);
}

SV3_1aPpParser::Ifndef_directiveContext* SV3_1aPpParser::Directive_in_macroContext::ifndef_directive() {
  return getRuleContext<SV3_1aPpParser::Ifndef_directiveContext>(0);
}

SV3_1aPpParser::Else_directiveContext* SV3_1aPpParser::Directive_in_macroContext::else_directive() {
  return getRuleContext<SV3_1aPpParser::Else_directiveContext>(0);
}

SV3_1aPpParser::Elsif_directiveContext* SV3_1aPpParser::Directive_in_macroContext::elsif_directive() {
  return getRuleContext<SV3_1aPpParser::Elsif_directiveContext>(0);
}

SV3_1aPpParser::Elseif_directiveContext* SV3_1aPpParser::Directive_in_macroContext::elseif_directive() {
  return getRuleContext<SV3_1aPpParser::Elseif_directiveContext>(0);
}

SV3_1aPpParser::Endif_directiveContext* SV3_1aPpParser::Directive_in_macroContext::endif_directive() {
  return getRuleContext<SV3_1aPpParser::Endif_directiveContext>(0);
}

SV3_1aPpParser::Include_directiveContext* SV3_1aPpParser::Directive_in_macroContext::include_directive() {
  return getRuleContext<SV3_1aPpParser::Include_directiveContext>(0);
}

SV3_1aPpParser::Resetall_directiveContext* SV3_1aPpParser::Directive_in_macroContext::resetall_directive() {
  return getRuleContext<SV3_1aPpParser::Resetall_directiveContext>(0);
}

SV3_1aPpParser::Timescale_directiveContext* SV3_1aPpParser::Directive_in_macroContext::timescale_directive() {
  return getRuleContext<SV3_1aPpParser::Timescale_directiveContext>(0);
}

SV3_1aPpParser::Unconnected_drive_directiveContext* SV3_1aPpParser::Directive_in_macroContext::unconnected_drive_directive() {
  return getRuleContext<SV3_1aPpParser::Unconnected_drive_directiveContext>(0);
}

SV3_1aPpParser::Nounconnected_drive_directiveContext* SV3_1aPpParser::Directive_in_macroContext::nounconnected_drive_directive() {
  return getRuleContext<SV3_1aPpParser::Nounconnected_drive_directiveContext>(0);
}

SV3_1aPpParser::Line_directiveContext* SV3_1aPpParser::Directive_in_macroContext::line_directive() {
  return getRuleContext<SV3_1aPpParser::Line_directiveContext>(0);
}

SV3_1aPpParser::Default_decay_time_directiveContext* SV3_1aPpParser::Directive_in_macroContext::default_decay_time_directive() {
  return getRuleContext<SV3_1aPpParser::Default_decay_time_directiveContext>(0);
}

SV3_1aPpParser::Default_trireg_strenght_directiveContext* SV3_1aPpParser::Directive_in_macroContext::default_trireg_strenght_directive() {
  return getRuleContext<SV3_1aPpParser::Default_trireg_strenght_directiveContext>(0);
}

SV3_1aPpParser::Delay_mode_distributed_directiveContext* SV3_1aPpParser::Directive_in_macroContext::delay_mode_distributed_directive() {
  return getRuleContext<SV3_1aPpParser::Delay_mode_distributed_directiveContext>(0);
}

SV3_1aPpParser::Delay_mode_path_directiveContext* SV3_1aPpParser::Directive_in_macroContext::delay_mode_path_directive() {
  return getRuleContext<SV3_1aPpParser::Delay_mode_path_directiveContext>(0);
}

SV3_1aPpParser::Delay_mode_unit_directiveContext* SV3_1aPpParser::Directive_in_macroContext::delay_mode_unit_directive() {
  return getRuleContext<SV3_1aPpParser::Delay_mode_unit_directiveContext>(0);
}

SV3_1aPpParser::Delay_mode_zero_directiveContext* SV3_1aPpParser::Directive_in_macroContext::delay_mode_zero_directive() {
  return getRuleContext<SV3_1aPpParser::Delay_mode_zero_directiveContext>(0);
}

SV3_1aPpParser::Protect_directiveContext* SV3_1aPpParser::Directive_in_macroContext::protect_directive() {
  return getRuleContext<SV3_1aPpParser::Protect_directiveContext>(0);
}

SV3_1aPpParser::Endprotect_directiveContext* SV3_1aPpParser::Directive_in_macroContext::endprotect_directive() {
  return getRuleContext<SV3_1aPpParser::Endprotect_directiveContext>(0);
}

SV3_1aPpParser::Protected_directiveContext* SV3_1aPpParser::Directive_in_macroContext::protected_directive() {
  return getRuleContext<SV3_1aPpParser::Protected_directiveContext>(0);
}

SV3_1aPpParser::Endprotected_directiveContext* SV3_1aPpParser::Directive_in_macroContext::endprotected_directive() {
  return getRuleContext<SV3_1aPpParser::Endprotected_directiveContext>(0);
}

SV3_1aPpParser::Expand_vectornets_directiveContext* SV3_1aPpParser::Directive_in_macroContext::expand_vectornets_directive() {
  return getRuleContext<SV3_1aPpParser::Expand_vectornets_directiveContext>(0);
}

SV3_1aPpParser::Noexpand_vectornets_directiveContext* SV3_1aPpParser::Directive_in_macroContext::noexpand_vectornets_directive() {
  return getRuleContext<SV3_1aPpParser::Noexpand_vectornets_directiveContext>(0);
}

SV3_1aPpParser::Autoexpand_vectornets_directiveContext* SV3_1aPpParser::Directive_in_macroContext::autoexpand_vectornets_directive() {
  return getRuleContext<SV3_1aPpParser::Autoexpand_vectornets_directiveContext>(0);
}

SV3_1aPpParser::Remove_gatename_directiveContext* SV3_1aPpParser::Directive_in_macroContext::remove_gatename_directive() {
  return getRuleContext<SV3_1aPpParser::Remove_gatename_directiveContext>(0);
}

SV3_1aPpParser::Noremove_gatenames_directiveContext* SV3_1aPpParser::Directive_in_macroContext::noremove_gatenames_directive() {
  return getRuleContext<SV3_1aPpParser::Noremove_gatenames_directiveContext>(0);
}

SV3_1aPpParser::Remove_netname_directiveContext* SV3_1aPpParser::Directive_in_macroContext::remove_netname_directive() {
  return getRuleContext<SV3_1aPpParser::Remove_netname_directiveContext>(0);
}

SV3_1aPpParser::Noremove_netnames_directiveContext* SV3_1aPpParser::Directive_in_macroContext::noremove_netnames_directive() {
  return getRuleContext<SV3_1aPpParser::Noremove_netnames_directiveContext>(0);
}

SV3_1aPpParser::Accelerate_directiveContext* SV3_1aPpParser::Directive_in_macroContext::accelerate_directive() {
  return getRuleContext<SV3_1aPpParser::Accelerate_directiveContext>(0);
}

SV3_1aPpParser::Noaccelerate_directiveContext* SV3_1aPpParser::Directive_in_macroContext::noaccelerate_directive() {
  return getRuleContext<SV3_1aPpParser::Noaccelerate_directiveContext>(0);
}

SV3_1aPpParser::Undefineall_directiveContext* SV3_1aPpParser::Directive_in_macroContext::undefineall_directive() {
  return getRuleContext<SV3_1aPpParser::Undefineall_directiveContext>(0);
}

SV3_1aPpParser::Uselib_directiveContext* SV3_1aPpParser::Directive_in_macroContext::uselib_directive() {
  return getRuleContext<SV3_1aPpParser::Uselib_directiveContext>(0);
}

SV3_1aPpParser::Disable_portfaults_directiveContext* SV3_1aPpParser::Directive_in_macroContext::disable_portfaults_directive() {
  return getRuleContext<SV3_1aPpParser::Disable_portfaults_directiveContext>(0);
}

SV3_1aPpParser::Enable_portfaults_directiveContext* SV3_1aPpParser::Directive_in_macroContext::enable_portfaults_directive() {
  return getRuleContext<SV3_1aPpParser::Enable_portfaults_directiveContext>(0);
}

SV3_1aPpParser::Nosuppress_faults_directiveContext* SV3_1aPpParser::Directive_in_macroContext::nosuppress_faults_directive() {
  return getRuleContext<SV3_1aPpParser::Nosuppress_faults_directiveContext>(0);
}

SV3_1aPpParser::Suppress_faults_directiveContext* SV3_1aPpParser::Directive_in_macroContext::suppress_faults_directive() {
  return getRuleContext<SV3_1aPpParser::Suppress_faults_directiveContext>(0);
}

SV3_1aPpParser::Signed_directiveContext* SV3_1aPpParser::Directive_in_macroContext::signed_directive() {
  return getRuleContext<SV3_1aPpParser::Signed_directiveContext>(0);
}

SV3_1aPpParser::Unsigned_directiveContext* SV3_1aPpParser::Directive_in_macroContext::unsigned_directive() {
  return getRuleContext<SV3_1aPpParser::Unsigned_directiveContext>(0);
}

SV3_1aPpParser::Sv_file_directiveContext* SV3_1aPpParser::Directive_in_macroContext::sv_file_directive() {
  return getRuleContext<SV3_1aPpParser::Sv_file_directiveContext>(0);
}

SV3_1aPpParser::Sv_line_directiveContext* SV3_1aPpParser::Directive_in_macroContext::sv_line_directive() {
  return getRuleContext<SV3_1aPpParser::Sv_line_directiveContext>(0);
}

SV3_1aPpParser::Sv_packageContext* SV3_1aPpParser::Directive_in_macroContext::sv_package() {
  return getRuleContext<SV3_1aPpParser::Sv_packageContext>(0);
}

SV3_1aPpParser::EndpackageContext* SV3_1aPpParser::Directive_in_macroContext::endpackage() {
  return getRuleContext<SV3_1aPpParser::EndpackageContext>(0);
}

SV3_1aPpParser::ModuleContext* SV3_1aPpParser::Directive_in_macroContext::module() {
  return getRuleContext<SV3_1aPpParser::ModuleContext>(0);
}

SV3_1aPpParser::EndmoduleContext* SV3_1aPpParser::Directive_in_macroContext::endmodule() {
  return getRuleContext<SV3_1aPpParser::EndmoduleContext>(0);
}

SV3_1aPpParser::Sv_interfaceContext* SV3_1aPpParser::Directive_in_macroContext::sv_interface() {
  return getRuleContext<SV3_1aPpParser::Sv_interfaceContext>(0);
}

SV3_1aPpParser::EndinterfaceContext* SV3_1aPpParser::Directive_in_macroContext::endinterface() {
  return getRuleContext<SV3_1aPpParser::EndinterfaceContext>(0);
}

SV3_1aPpParser::ProgramContext* SV3_1aPpParser::Directive_in_macroContext::program() {
  return getRuleContext<SV3_1aPpParser::ProgramContext>(0);
}

SV3_1aPpParser::EndprogramContext* SV3_1aPpParser::Directive_in_macroContext::endprogram() {
  return getRuleContext<SV3_1aPpParser::EndprogramContext>(0);
}

SV3_1aPpParser::PrimitiveContext* SV3_1aPpParser::Directive_in_macroContext::primitive() {
  return getRuleContext<SV3_1aPpParser::PrimitiveContext>(0);
}

SV3_1aPpParser::EndprimitiveContext* SV3_1aPpParser::Directive_in_macroContext::endprimitive() {
  return getRuleContext<SV3_1aPpParser::EndprimitiveContext>(0);
}

SV3_1aPpParser::CheckerContext* SV3_1aPpParser::Directive_in_macroContext::checker() {
  return getRuleContext<SV3_1aPpParser::CheckerContext>(0);
}

SV3_1aPpParser::EndcheckerContext* SV3_1aPpParser::Directive_in_macroContext::endchecker() {
  return getRuleContext<SV3_1aPpParser::EndcheckerContext>(0);
}

SV3_1aPpParser::ConfigContext* SV3_1aPpParser::Directive_in_macroContext::config() {
  return getRuleContext<SV3_1aPpParser::ConfigContext>(0);
}

SV3_1aPpParser::EndconfigContext* SV3_1aPpParser::Directive_in_macroContext::endconfig() {
  return getRuleContext<SV3_1aPpParser::EndconfigContext>(0);
}

SV3_1aPpParser::Simple_args_macro_definition_in_macro_bodyContext* SV3_1aPpParser::Directive_in_macroContext::simple_args_macro_definition_in_macro_body() {
  return getRuleContext<SV3_1aPpParser::Simple_args_macro_definition_in_macro_bodyContext>(0);
}

SV3_1aPpParser::Simple_no_args_macro_definition_in_macro_bodyContext* SV3_1aPpParser::Directive_in_macroContext::simple_no_args_macro_definition_in_macro_body() {
  return getRuleContext<SV3_1aPpParser::Simple_no_args_macro_definition_in_macro_bodyContext>(0);
}

SV3_1aPpParser::Pound_delayContext* SV3_1aPpParser::Directive_in_macroContext::pound_delay() {
  return getRuleContext<SV3_1aPpParser::Pound_delayContext>(0);
}

SV3_1aPpParser::Pound_pound_delayContext* SV3_1aPpParser::Directive_in_macroContext::pound_pound_delay() {
  return getRuleContext<SV3_1aPpParser::Pound_pound_delayContext>(0);
}


size_t SV3_1aPpParser::Directive_in_macroContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleDirective_in_macro;
}

void SV3_1aPpParser::Directive_in_macroContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterDirective_in_macro(this);
}

void SV3_1aPpParser::Directive_in_macroContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitDirective_in_macro(this);
}

SV3_1aPpParser::Directive_in_macroContext* SV3_1aPpParser::directive_in_macro() {
  Directive_in_macroContext *_localctx = _tracker.createInstance<Directive_in_macroContext>(_ctx, getState());
  enterRule(_localctx, 172, SV3_1aPpParser::RuleDirective_in_macro);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    setState(804);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 47, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(741);
      celldefine_directive();
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(742);
      endcelldefine_directive();
      break;
    }

    case 3: {
      enterOuterAlt(_localctx, 3);
      setState(743);
      default_nettype_directive();
      break;
    }

    case 4: {
      enterOuterAlt(_localctx, 4);
      setState(744);
      undef_directive();
      break;
    }

    case 5: {
      enterOuterAlt(_localctx, 5);
      setState(745);
      ifdef_directive();
      break;
    }

    case 6: {
      enterOuterAlt(_localctx, 6);
      setState(746);
      ifndef_directive();
      break;
    }

    case 7: {
      enterOuterAlt(_localctx, 7);
      setState(747);
      else_directive();
      break;
    }

    case 8: {
      enterOuterAlt(_localctx, 8);
      setState(748);
      elsif_directive();
      break;
    }

    case 9: {
      enterOuterAlt(_localctx, 9);
      setState(749);
      elseif_directive();
      break;
    }

    case 10: {
      enterOuterAlt(_localctx, 10);
      setState(750);
      endif_directive();
      break;
    }

    case 11: {
      enterOuterAlt(_localctx, 11);
      setState(751);
      include_directive();
      break;
    }

    case 12: {
      enterOuterAlt(_localctx, 12);
      setState(752);
      resetall_directive();
      break;
    }

    case 13: {
      enterOuterAlt(_localctx, 13);
      setState(753);
      timescale_directive();
      break;
    }

    case 14: {
      enterOuterAlt(_localctx, 14);
      setState(754);
      unconnected_drive_directive();
      break;
    }

    case 15: {
      enterOuterAlt(_localctx, 15);
      setState(755);
      nounconnected_drive_directive();
      break;
    }

    case 16: {
      enterOuterAlt(_localctx, 16);
      setState(756);
      line_directive();
      break;
    }

    case 17: {
      enterOuterAlt(_localctx, 17);
      setState(757);
      default_decay_time_directive();
      break;
    }

    case 18: {
      enterOuterAlt(_localctx, 18);
      setState(758);
      default_trireg_strenght_directive();
      break;
    }

    case 19: {
      enterOuterAlt(_localctx, 19);
      setState(759);
      delay_mode_distributed_directive();
      break;
    }

    case 20: {
      enterOuterAlt(_localctx, 20);
      setState(760);
      delay_mode_path_directive();
      break;
    }

    case 21: {
      enterOuterAlt(_localctx, 21);
      setState(761);
      delay_mode_unit_directive();
      break;
    }

    case 22: {
      enterOuterAlt(_localctx, 22);
      setState(762);
      delay_mode_zero_directive();
      break;
    }

    case 23: {
      enterOuterAlt(_localctx, 23);
      setState(763);
      protect_directive();
      break;
    }

    case 24: {
      enterOuterAlt(_localctx, 24);
      setState(764);
      endprotect_directive();
      break;
    }

    case 25: {
      enterOuterAlt(_localctx, 25);
      setState(765);
      protected_directive();
      break;
    }

    case 26: {
      enterOuterAlt(_localctx, 26);
      setState(766);
      endprotected_directive();
      break;
    }

    case 27: {
      enterOuterAlt(_localctx, 27);
      setState(767);
      expand_vectornets_directive();
      break;
    }

    case 28: {
      enterOuterAlt(_localctx, 28);
      setState(768);
      noexpand_vectornets_directive();
      break;
    }

    case 29: {
      enterOuterAlt(_localctx, 29);
      setState(769);
      autoexpand_vectornets_directive();
      break;
    }

    case 30: {
      enterOuterAlt(_localctx, 30);
      setState(770);
      remove_gatename_directive();
      break;
    }

    case 31: {
      enterOuterAlt(_localctx, 31);
      setState(771);
      noremove_gatenames_directive();
      break;
    }

    case 32: {
      enterOuterAlt(_localctx, 32);
      setState(772);
      remove_netname_directive();
      break;
    }

    case 33: {
      enterOuterAlt(_localctx, 33);
      setState(773);
      noremove_netnames_directive();
      break;
    }

    case 34: {
      enterOuterAlt(_localctx, 34);
      setState(774);
      accelerate_directive();
      break;
    }

    case 35: {
      enterOuterAlt(_localctx, 35);
      setState(775);
      noaccelerate_directive();
      break;
    }

    case 36: {
      enterOuterAlt(_localctx, 36);
      setState(776);
      undefineall_directive();
      break;
    }

    case 37: {
      enterOuterAlt(_localctx, 37);
      setState(777);
      uselib_directive();
      break;
    }

    case 38: {
      enterOuterAlt(_localctx, 38);
      setState(778);
      disable_portfaults_directive();
      break;
    }

    case 39: {
      enterOuterAlt(_localctx, 39);
      setState(779);
      enable_portfaults_directive();
      break;
    }

    case 40: {
      enterOuterAlt(_localctx, 40);
      setState(780);
      nosuppress_faults_directive();
      break;
    }

    case 41: {
      enterOuterAlt(_localctx, 41);
      setState(781);
      suppress_faults_directive();
      break;
    }

    case 42: {
      enterOuterAlt(_localctx, 42);
      setState(782);
      signed_directive();
      break;
    }

    case 43: {
      enterOuterAlt(_localctx, 43);
      setState(783);
      unsigned_directive();
      break;
    }

    case 44: {
      enterOuterAlt(_localctx, 44);
      setState(784);
      sv_file_directive();
      break;
    }

    case 45: {
      enterOuterAlt(_localctx, 45);
      setState(785);
      sv_line_directive();
      break;
    }

    case 46: {
      enterOuterAlt(_localctx, 46);
      setState(786);
      sv_package();
      break;
    }

    case 47: {
      enterOuterAlt(_localctx, 47);
      setState(787);
      endpackage();
      break;
    }

    case 48: {
      enterOuterAlt(_localctx, 48);
      setState(788);
      module();
      break;
    }

    case 49: {
      enterOuterAlt(_localctx, 49);
      setState(789);
      endmodule();
      break;
    }

    case 50: {
      enterOuterAlt(_localctx, 50);
      setState(790);
      sv_interface();
      break;
    }

    case 51: {
      enterOuterAlt(_localctx, 51);
      setState(791);
      endinterface();
      break;
    }

    case 52: {
      enterOuterAlt(_localctx, 52);
      setState(792);
      program();
      break;
    }

    case 53: {
      enterOuterAlt(_localctx, 53);
      setState(793);
      endprogram();
      break;
    }

    case 54: {
      enterOuterAlt(_localctx, 54);
      setState(794);
      primitive();
      break;
    }

    case 55: {
      enterOuterAlt(_localctx, 55);
      setState(795);
      endprimitive();
      break;
    }

    case 56: {
      enterOuterAlt(_localctx, 56);
      setState(796);
      checker();
      break;
    }

    case 57: {
      enterOuterAlt(_localctx, 57);
      setState(797);
      endchecker();
      break;
    }

    case 58: {
      enterOuterAlt(_localctx, 58);
      setState(798);
      config();
      break;
    }

    case 59: {
      enterOuterAlt(_localctx, 59);
      setState(799);
      endconfig();
      break;
    }

    case 60: {
      enterOuterAlt(_localctx, 60);
      setState(800);
      simple_args_macro_definition_in_macro_body();
      break;
    }

    case 61: {
      enterOuterAlt(_localctx, 61);
      setState(801);
      simple_no_args_macro_definition_in_macro_body();
      break;
    }

    case 62: {
      enterOuterAlt(_localctx, 62);
      setState(802);
      pound_delay();
      break;
    }

    case 63: {
      enterOuterAlt(_localctx, 63);
      setState(803);
      pound_pound_delay();
      break;
    }

    default:
      break;
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Macro_argumentsContext ------------------------------------------------------------------

SV3_1aPpParser::Macro_argumentsContext::Macro_argumentsContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Macro_argumentsContext::PARENS_OPEN() {
  return getToken(SV3_1aPpParser::PARENS_OPEN, 0);
}

tree::TerminalNode* SV3_1aPpParser::Macro_argumentsContext::PARENS_CLOSE() {
  return getToken(SV3_1aPpParser::PARENS_CLOSE, 0);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Macro_argumentsContext::Simple_identifier() {
  return getTokens(SV3_1aPpParser::Simple_identifier);
}

tree::TerminalNode* SV3_1aPpParser::Macro_argumentsContext::Simple_identifier(size_t i) {
  return getToken(SV3_1aPpParser::Simple_identifier, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Macro_argumentsContext::COMMA() {
  return getTokens(SV3_1aPpParser::COMMA);
}

tree::TerminalNode* SV3_1aPpParser::Macro_argumentsContext::COMMA(size_t i) {
  return getToken(SV3_1aPpParser::COMMA, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Macro_argumentsContext::Spaces() {
  return getTokens(SV3_1aPpParser::Spaces);
}

tree::TerminalNode* SV3_1aPpParser::Macro_argumentsContext::Spaces(size_t i) {
  return getToken(SV3_1aPpParser::Spaces, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Macro_argumentsContext::EQUAL_OP() {
  return getTokens(SV3_1aPpParser::EQUAL_OP);
}

tree::TerminalNode* SV3_1aPpParser::Macro_argumentsContext::EQUAL_OP(size_t i) {
  return getToken(SV3_1aPpParser::EQUAL_OP, i);
}

std::vector<SV3_1aPpParser::Default_valueContext *> SV3_1aPpParser::Macro_argumentsContext::default_value() {
  return getRuleContexts<SV3_1aPpParser::Default_valueContext>();
}

SV3_1aPpParser::Default_valueContext* SV3_1aPpParser::Macro_argumentsContext::default_value(size_t i) {
  return getRuleContext<SV3_1aPpParser::Default_valueContext>(i);
}


size_t SV3_1aPpParser::Macro_argumentsContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleMacro_arguments;
}

void SV3_1aPpParser::Macro_argumentsContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterMacro_arguments(this);
}

void SV3_1aPpParser::Macro_argumentsContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitMacro_arguments(this);
}

SV3_1aPpParser::Macro_argumentsContext* SV3_1aPpParser::macro_arguments() {
  Macro_argumentsContext *_localctx = _tracker.createInstance<Macro_argumentsContext>(_ctx, getState());
  enterRule(_localctx, 174, SV3_1aPpParser::RuleMacro_arguments);
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    size_t alt;
    enterOuterAlt(_localctx, 1);
    setState(806);
    match(SV3_1aPpParser::PARENS_OPEN);
    setState(859);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (_la == SV3_1aPpParser::Simple_identifier) {
      setState(807);
      match(SV3_1aPpParser::Simple_identifier);
      setState(811);
      _errHandler->sync(this);
      _la = _input->LA(1);
      while (_la == SV3_1aPpParser::Spaces) {
        setState(808);
        match(SV3_1aPpParser::Spaces);
        setState(813);
        _errHandler->sync(this);
        _la = _input->LA(1);
      }
      setState(823);
      _errHandler->sync(this);
      _la = _input->LA(1);
      while (_la == SV3_1aPpParser::EQUAL_OP) {
        setState(814);
        match(SV3_1aPpParser::EQUAL_OP);
        setState(818);
        _errHandler->sync(this);
        alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 49, _ctx);
        while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
          if (alt == 1) {
            setState(815);
            default_value(); 
          }
          setState(820);
          _errHandler->sync(this);
          alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 49, _ctx);
        }
        setState(825);
        _errHandler->sync(this);
        _la = _input->LA(1);
      }
      setState(854);
      _errHandler->sync(this);
      _la = _input->LA(1);
      while (_la == SV3_1aPpParser::COMMA) {
        setState(826);
        match(SV3_1aPpParser::COMMA);
        setState(830);
        _errHandler->sync(this);
        _la = _input->LA(1);
        while (_la == SV3_1aPpParser::Spaces) {
          setState(827);
          match(SV3_1aPpParser::Spaces);
          setState(832);
          _errHandler->sync(this);
          _la = _input->LA(1);
        }

        setState(833);
        match(SV3_1aPpParser::Simple_identifier);
        setState(837);
        _errHandler->sync(this);
        _la = _input->LA(1);
        while (_la == SV3_1aPpParser::Spaces) {
          setState(834);
          match(SV3_1aPpParser::Spaces);
          setState(839);
          _errHandler->sync(this);
          _la = _input->LA(1);
        }
        setState(849);
        _errHandler->sync(this);
        _la = _input->LA(1);
        while (_la == SV3_1aPpParser::EQUAL_OP) {
          setState(840);
          match(SV3_1aPpParser::EQUAL_OP);
          setState(844);
          _errHandler->sync(this);
          alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 53, _ctx);
          while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
            if (alt == 1) {
              setState(841);
              default_value(); 
            }
            setState(846);
            _errHandler->sync(this);
            alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 53, _ctx);
          }
          setState(851);
          _errHandler->sync(this);
          _la = _input->LA(1);
        }
        setState(856);
        _errHandler->sync(this);
        _la = _input->LA(1);
      }
      setState(861);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
    setState(862);
    match(SV3_1aPpParser::PARENS_CLOSE);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Escaped_macro_definition_bodyContext ------------------------------------------------------------------

SV3_1aPpParser::Escaped_macro_definition_bodyContext::Escaped_macro_definition_bodyContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

SV3_1aPpParser::Escaped_macro_definition_body_alt1Context* SV3_1aPpParser::Escaped_macro_definition_bodyContext::escaped_macro_definition_body_alt1() {
  return getRuleContext<SV3_1aPpParser::Escaped_macro_definition_body_alt1Context>(0);
}

SV3_1aPpParser::Escaped_macro_definition_body_alt2Context* SV3_1aPpParser::Escaped_macro_definition_bodyContext::escaped_macro_definition_body_alt2() {
  return getRuleContext<SV3_1aPpParser::Escaped_macro_definition_body_alt2Context>(0);
}


size_t SV3_1aPpParser::Escaped_macro_definition_bodyContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleEscaped_macro_definition_body;
}

void SV3_1aPpParser::Escaped_macro_definition_bodyContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterEscaped_macro_definition_body(this);
}

void SV3_1aPpParser::Escaped_macro_definition_bodyContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitEscaped_macro_definition_body(this);
}

SV3_1aPpParser::Escaped_macro_definition_bodyContext* SV3_1aPpParser::escaped_macro_definition_body() {
  Escaped_macro_definition_bodyContext *_localctx = _tracker.createInstance<Escaped_macro_definition_bodyContext>(_ctx, getState());
  enterRule(_localctx, 176, SV3_1aPpParser::RuleEscaped_macro_definition_body);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    setState(866);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 57, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(864);
      escaped_macro_definition_body_alt1();
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(865);
      escaped_macro_definition_body_alt2();
      break;
    }

    default:
      break;
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Escaped_macro_definition_body_alt1Context ------------------------------------------------------------------

SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::Escaped_macro_definition_body_alt1Context(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::ESCAPED_CR() {
  return getTokens(SV3_1aPpParser::ESCAPED_CR);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::ESCAPED_CR(size_t i) {
  return getToken(SV3_1aPpParser::ESCAPED_CR, i);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::CR() {
  return getToken(SV3_1aPpParser::CR, 0);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::EOF() {
  return getToken(SV3_1aPpParser::EOF, 0);
}

std::vector<SV3_1aPpParser::Unterminated_stringContext *> SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::unterminated_string() {
  return getRuleContexts<SV3_1aPpParser::Unterminated_stringContext>();
}

SV3_1aPpParser::Unterminated_stringContext* SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::unterminated_string(size_t i) {
  return getRuleContext<SV3_1aPpParser::Unterminated_stringContext>(i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::Macro_identifier() {
  return getTokens(SV3_1aPpParser::Macro_identifier);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::Macro_identifier(size_t i) {
  return getToken(SV3_1aPpParser::Macro_identifier, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::Macro_Escaped_identifier() {
  return getTokens(SV3_1aPpParser::Macro_Escaped_identifier);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::Macro_Escaped_identifier(size_t i) {
  return getToken(SV3_1aPpParser::Macro_Escaped_identifier, i);
}

std::vector<SV3_1aPpParser::Escaped_identifierContext *> SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::escaped_identifier() {
  return getRuleContexts<SV3_1aPpParser::Escaped_identifierContext>();
}

SV3_1aPpParser::Escaped_identifierContext* SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::escaped_identifier(size_t i) {
  return getRuleContext<SV3_1aPpParser::Escaped_identifierContext>(i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::Simple_identifier() {
  return getTokens(SV3_1aPpParser::Simple_identifier);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::Simple_identifier(size_t i) {
  return getToken(SV3_1aPpParser::Simple_identifier, i);
}

std::vector<SV3_1aPpParser::NumberContext *> SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::number() {
  return getRuleContexts<SV3_1aPpParser::NumberContext>();
}

SV3_1aPpParser::NumberContext* SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::number(size_t i) {
  return getRuleContext<SV3_1aPpParser::NumberContext>(i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::TEXT_CR() {
  return getTokens(SV3_1aPpParser::TEXT_CR);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::TEXT_CR(size_t i) {
  return getToken(SV3_1aPpParser::TEXT_CR, i);
}

std::vector<SV3_1aPpParser::Pound_delayContext *> SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::pound_delay() {
  return getRuleContexts<SV3_1aPpParser::Pound_delayContext>();
}

SV3_1aPpParser::Pound_delayContext* SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::pound_delay(size_t i) {
  return getRuleContext<SV3_1aPpParser::Pound_delayContext>(i);
}

std::vector<SV3_1aPpParser::Pound_pound_delayContext *> SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::pound_pound_delay() {
  return getRuleContexts<SV3_1aPpParser::Pound_pound_delayContext>();
}

SV3_1aPpParser::Pound_pound_delayContext* SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::pound_pound_delay(size_t i) {
  return getRuleContext<SV3_1aPpParser::Pound_pound_delayContext>(i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::PARENS_OPEN() {
  return getTokens(SV3_1aPpParser::PARENS_OPEN);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::PARENS_OPEN(size_t i) {
  return getToken(SV3_1aPpParser::PARENS_OPEN, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::PARENS_CLOSE() {
  return getTokens(SV3_1aPpParser::PARENS_CLOSE);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::PARENS_CLOSE(size_t i) {
  return getToken(SV3_1aPpParser::PARENS_CLOSE, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::COMMA() {
  return getTokens(SV3_1aPpParser::COMMA);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::COMMA(size_t i) {
  return getToken(SV3_1aPpParser::COMMA, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::EQUAL_OP() {
  return getTokens(SV3_1aPpParser::EQUAL_OP);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::EQUAL_OP(size_t i) {
  return getToken(SV3_1aPpParser::EQUAL_OP, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::DOUBLE_QUOTE() {
  return getTokens(SV3_1aPpParser::DOUBLE_QUOTE);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::DOUBLE_QUOTE(size_t i) {
  return getToken(SV3_1aPpParser::DOUBLE_QUOTE, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::TICK_VARIABLE() {
  return getTokens(SV3_1aPpParser::TICK_VARIABLE);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::TICK_VARIABLE(size_t i) {
  return getToken(SV3_1aPpParser::TICK_VARIABLE, i);
}

std::vector<SV3_1aPpParser::Directive_in_macroContext *> SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::directive_in_macro() {
  return getRuleContexts<SV3_1aPpParser::Directive_in_macroContext>();
}

SV3_1aPpParser::Directive_in_macroContext* SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::directive_in_macro(size_t i) {
  return getRuleContext<SV3_1aPpParser::Directive_in_macroContext>(i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::Spaces() {
  return getTokens(SV3_1aPpParser::Spaces);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::Spaces(size_t i) {
  return getToken(SV3_1aPpParser::Spaces, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::Fixed_point_number() {
  return getTokens(SV3_1aPpParser::Fixed_point_number);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::Fixed_point_number(size_t i) {
  return getToken(SV3_1aPpParser::Fixed_point_number, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::String() {
  return getTokens(SV3_1aPpParser::String);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::String(size_t i) {
  return getToken(SV3_1aPpParser::String, i);
}

std::vector<SV3_1aPpParser::CommentsContext *> SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::comments() {
  return getRuleContexts<SV3_1aPpParser::CommentsContext>();
}

SV3_1aPpParser::CommentsContext* SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::comments(size_t i) {
  return getRuleContext<SV3_1aPpParser::CommentsContext>(i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::TICK_QUOTE() {
  return getTokens(SV3_1aPpParser::TICK_QUOTE);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::TICK_QUOTE(size_t i) {
  return getToken(SV3_1aPpParser::TICK_QUOTE, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::TICK_BACKSLASH_TICK_QUOTE() {
  return getTokens(SV3_1aPpParser::TICK_BACKSLASH_TICK_QUOTE);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::TICK_BACKSLASH_TICK_QUOTE(size_t i) {
  return getToken(SV3_1aPpParser::TICK_BACKSLASH_TICK_QUOTE, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::TICK_TICK() {
  return getTokens(SV3_1aPpParser::TICK_TICK);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::TICK_TICK(size_t i) {
  return getToken(SV3_1aPpParser::TICK_TICK, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::Special() {
  return getTokens(SV3_1aPpParser::Special);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::Special(size_t i) {
  return getToken(SV3_1aPpParser::Special, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::CURLY_OPEN() {
  return getTokens(SV3_1aPpParser::CURLY_OPEN);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::CURLY_OPEN(size_t i) {
  return getToken(SV3_1aPpParser::CURLY_OPEN, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::CURLY_CLOSE() {
  return getTokens(SV3_1aPpParser::CURLY_CLOSE);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::CURLY_CLOSE(size_t i) {
  return getToken(SV3_1aPpParser::CURLY_CLOSE, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::SQUARE_OPEN() {
  return getTokens(SV3_1aPpParser::SQUARE_OPEN);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::SQUARE_OPEN(size_t i) {
  return getToken(SV3_1aPpParser::SQUARE_OPEN, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::SQUARE_CLOSE() {
  return getTokens(SV3_1aPpParser::SQUARE_CLOSE);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::SQUARE_CLOSE(size_t i) {
  return getToken(SV3_1aPpParser::SQUARE_CLOSE, i);
}


size_t SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::getRuleIndex() const {
  return SV3_1aPpParser::RuleEscaped_macro_definition_body_alt1;
}

void SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterEscaped_macro_definition_body_alt1(this);
}

void SV3_1aPpParser::Escaped_macro_definition_body_alt1Context::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitEscaped_macro_definition_body_alt1(this);
}

SV3_1aPpParser::Escaped_macro_definition_body_alt1Context* SV3_1aPpParser::escaped_macro_definition_body_alt1() {
  Escaped_macro_definition_body_alt1Context *_localctx = _tracker.createInstance<Escaped_macro_definition_body_alt1Context>(_ctx, getState());
  enterRule(_localctx, 178, SV3_1aPpParser::RuleEscaped_macro_definition_body_alt1);
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    size_t alt;
    enterOuterAlt(_localctx, 1);
    setState(899);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 59, _ctx);
    while (alt != 1 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1 + 1) {
        setState(897);
        _errHandler->sync(this);
        switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 58, _ctx)) {
        case 1: {
          setState(868);
          unterminated_string();
          break;
        }

        case 2: {
          setState(869);
          match(SV3_1aPpParser::Macro_identifier);
          break;
        }

        case 3: {
          setState(870);
          match(SV3_1aPpParser::Macro_Escaped_identifier);
          break;
        }

        case 4: {
          setState(871);
          escaped_identifier();
          break;
        }

        case 5: {
          setState(872);
          match(SV3_1aPpParser::Simple_identifier);
          break;
        }

        case 6: {
          setState(873);
          number();
          break;
        }

        case 7: {
          setState(874);
          match(SV3_1aPpParser::TEXT_CR);
          break;
        }

        case 8: {
          setState(875);
          pound_delay();
          break;
        }

        case 9: {
          setState(876);
          pound_pound_delay();
          break;
        }

        case 10: {
          setState(877);
          match(SV3_1aPpParser::ESCAPED_CR);
          break;
        }

        case 11: {
          setState(878);
          match(SV3_1aPpParser::PARENS_OPEN);
          break;
        }

        case 12: {
          setState(879);
          match(SV3_1aPpParser::PARENS_CLOSE);
          break;
        }

        case 13: {
          setState(880);
          match(SV3_1aPpParser::COMMA);
          break;
        }

        case 14: {
          setState(881);
          match(SV3_1aPpParser::EQUAL_OP);
          break;
        }

        case 15: {
          setState(882);
          match(SV3_1aPpParser::DOUBLE_QUOTE);
          break;
        }

        case 16: {
          setState(883);
          match(SV3_1aPpParser::TICK_VARIABLE);
          break;
        }

        case 17: {
          setState(884);
          directive_in_macro();
          break;
        }

        case 18: {
          setState(885);
          match(SV3_1aPpParser::Spaces);
          break;
        }

        case 19: {
          setState(886);
          match(SV3_1aPpParser::Fixed_point_number);
          break;
        }

        case 20: {
          setState(887);
          match(SV3_1aPpParser::String);
          break;
        }

        case 21: {
          setState(888);
          comments();
          break;
        }

        case 22: {
          setState(889);
          match(SV3_1aPpParser::TICK_QUOTE);
          break;
        }

        case 23: {
          setState(890);
          match(SV3_1aPpParser::TICK_BACKSLASH_TICK_QUOTE);
          break;
        }

        case 24: {
          setState(891);
          match(SV3_1aPpParser::TICK_TICK);
          break;
        }

        case 25: {
          setState(892);
          match(SV3_1aPpParser::Special);
          break;
        }

        case 26: {
          setState(893);
          match(SV3_1aPpParser::CURLY_OPEN);
          break;
        }

        case 27: {
          setState(894);
          match(SV3_1aPpParser::CURLY_CLOSE);
          break;
        }

        case 28: {
          setState(895);
          match(SV3_1aPpParser::SQUARE_OPEN);
          break;
        }

        case 29: {
          setState(896);
          match(SV3_1aPpParser::SQUARE_CLOSE);
          break;
        }

        default:
          break;
        } 
      }
      setState(901);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 59, _ctx);
    }
    setState(902);
    match(SV3_1aPpParser::ESCAPED_CR);
    setState(906);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (_la == SV3_1aPpParser::Spaces) {
      setState(903);
      match(SV3_1aPpParser::Spaces);
      setState(908);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
    setState(909);
    _la = _input->LA(1);
    if (!(_la == SV3_1aPpParser::EOF || _la == SV3_1aPpParser::CR)) {
    _errHandler->recoverInline(this);
    }
    else {
      _errHandler->reportMatch(this);
      consume();
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Escaped_macro_definition_body_alt2Context ------------------------------------------------------------------

SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::Escaped_macro_definition_body_alt2Context(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::CR() {
  return getToken(SV3_1aPpParser::CR, 0);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::EOF() {
  return getToken(SV3_1aPpParser::EOF, 0);
}

std::vector<SV3_1aPpParser::Unterminated_stringContext *> SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::unterminated_string() {
  return getRuleContexts<SV3_1aPpParser::Unterminated_stringContext>();
}

SV3_1aPpParser::Unterminated_stringContext* SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::unterminated_string(size_t i) {
  return getRuleContext<SV3_1aPpParser::Unterminated_stringContext>(i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::Macro_identifier() {
  return getTokens(SV3_1aPpParser::Macro_identifier);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::Macro_identifier(size_t i) {
  return getToken(SV3_1aPpParser::Macro_identifier, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::Macro_Escaped_identifier() {
  return getTokens(SV3_1aPpParser::Macro_Escaped_identifier);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::Macro_Escaped_identifier(size_t i) {
  return getToken(SV3_1aPpParser::Macro_Escaped_identifier, i);
}

std::vector<SV3_1aPpParser::Escaped_identifierContext *> SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::escaped_identifier() {
  return getRuleContexts<SV3_1aPpParser::Escaped_identifierContext>();
}

SV3_1aPpParser::Escaped_identifierContext* SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::escaped_identifier(size_t i) {
  return getRuleContext<SV3_1aPpParser::Escaped_identifierContext>(i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::Simple_identifier() {
  return getTokens(SV3_1aPpParser::Simple_identifier);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::Simple_identifier(size_t i) {
  return getToken(SV3_1aPpParser::Simple_identifier, i);
}

std::vector<SV3_1aPpParser::NumberContext *> SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::number() {
  return getRuleContexts<SV3_1aPpParser::NumberContext>();
}

SV3_1aPpParser::NumberContext* SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::number(size_t i) {
  return getRuleContext<SV3_1aPpParser::NumberContext>(i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::TEXT_CR() {
  return getTokens(SV3_1aPpParser::TEXT_CR);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::TEXT_CR(size_t i) {
  return getToken(SV3_1aPpParser::TEXT_CR, i);
}

std::vector<SV3_1aPpParser::Pound_delayContext *> SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::pound_delay() {
  return getRuleContexts<SV3_1aPpParser::Pound_delayContext>();
}

SV3_1aPpParser::Pound_delayContext* SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::pound_delay(size_t i) {
  return getRuleContext<SV3_1aPpParser::Pound_delayContext>(i);
}

std::vector<SV3_1aPpParser::Pound_pound_delayContext *> SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::pound_pound_delay() {
  return getRuleContexts<SV3_1aPpParser::Pound_pound_delayContext>();
}

SV3_1aPpParser::Pound_pound_delayContext* SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::pound_pound_delay(size_t i) {
  return getRuleContext<SV3_1aPpParser::Pound_pound_delayContext>(i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::ESCAPED_CR() {
  return getTokens(SV3_1aPpParser::ESCAPED_CR);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::ESCAPED_CR(size_t i) {
  return getToken(SV3_1aPpParser::ESCAPED_CR, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::PARENS_OPEN() {
  return getTokens(SV3_1aPpParser::PARENS_OPEN);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::PARENS_OPEN(size_t i) {
  return getToken(SV3_1aPpParser::PARENS_OPEN, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::PARENS_CLOSE() {
  return getTokens(SV3_1aPpParser::PARENS_CLOSE);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::PARENS_CLOSE(size_t i) {
  return getToken(SV3_1aPpParser::PARENS_CLOSE, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::COMMA() {
  return getTokens(SV3_1aPpParser::COMMA);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::COMMA(size_t i) {
  return getToken(SV3_1aPpParser::COMMA, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::EQUAL_OP() {
  return getTokens(SV3_1aPpParser::EQUAL_OP);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::EQUAL_OP(size_t i) {
  return getToken(SV3_1aPpParser::EQUAL_OP, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::DOUBLE_QUOTE() {
  return getTokens(SV3_1aPpParser::DOUBLE_QUOTE);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::DOUBLE_QUOTE(size_t i) {
  return getToken(SV3_1aPpParser::DOUBLE_QUOTE, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::TICK_VARIABLE() {
  return getTokens(SV3_1aPpParser::TICK_VARIABLE);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::TICK_VARIABLE(size_t i) {
  return getToken(SV3_1aPpParser::TICK_VARIABLE, i);
}

std::vector<SV3_1aPpParser::Directive_in_macroContext *> SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::directive_in_macro() {
  return getRuleContexts<SV3_1aPpParser::Directive_in_macroContext>();
}

SV3_1aPpParser::Directive_in_macroContext* SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::directive_in_macro(size_t i) {
  return getRuleContext<SV3_1aPpParser::Directive_in_macroContext>(i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::Spaces() {
  return getTokens(SV3_1aPpParser::Spaces);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::Spaces(size_t i) {
  return getToken(SV3_1aPpParser::Spaces, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::Fixed_point_number() {
  return getTokens(SV3_1aPpParser::Fixed_point_number);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::Fixed_point_number(size_t i) {
  return getToken(SV3_1aPpParser::Fixed_point_number, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::String() {
  return getTokens(SV3_1aPpParser::String);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::String(size_t i) {
  return getToken(SV3_1aPpParser::String, i);
}

std::vector<SV3_1aPpParser::CommentsContext *> SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::comments() {
  return getRuleContexts<SV3_1aPpParser::CommentsContext>();
}

SV3_1aPpParser::CommentsContext* SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::comments(size_t i) {
  return getRuleContext<SV3_1aPpParser::CommentsContext>(i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::TICK_QUOTE() {
  return getTokens(SV3_1aPpParser::TICK_QUOTE);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::TICK_QUOTE(size_t i) {
  return getToken(SV3_1aPpParser::TICK_QUOTE, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::TICK_BACKSLASH_TICK_QUOTE() {
  return getTokens(SV3_1aPpParser::TICK_BACKSLASH_TICK_QUOTE);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::TICK_BACKSLASH_TICK_QUOTE(size_t i) {
  return getToken(SV3_1aPpParser::TICK_BACKSLASH_TICK_QUOTE, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::TICK_TICK() {
  return getTokens(SV3_1aPpParser::TICK_TICK);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::TICK_TICK(size_t i) {
  return getToken(SV3_1aPpParser::TICK_TICK, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::Special() {
  return getTokens(SV3_1aPpParser::Special);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::Special(size_t i) {
  return getToken(SV3_1aPpParser::Special, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::CURLY_OPEN() {
  return getTokens(SV3_1aPpParser::CURLY_OPEN);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::CURLY_OPEN(size_t i) {
  return getToken(SV3_1aPpParser::CURLY_OPEN, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::CURLY_CLOSE() {
  return getTokens(SV3_1aPpParser::CURLY_CLOSE);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::CURLY_CLOSE(size_t i) {
  return getToken(SV3_1aPpParser::CURLY_CLOSE, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::SQUARE_OPEN() {
  return getTokens(SV3_1aPpParser::SQUARE_OPEN);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::SQUARE_OPEN(size_t i) {
  return getToken(SV3_1aPpParser::SQUARE_OPEN, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::SQUARE_CLOSE() {
  return getTokens(SV3_1aPpParser::SQUARE_CLOSE);
}

tree::TerminalNode* SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::SQUARE_CLOSE(size_t i) {
  return getToken(SV3_1aPpParser::SQUARE_CLOSE, i);
}


size_t SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::getRuleIndex() const {
  return SV3_1aPpParser::RuleEscaped_macro_definition_body_alt2;
}

void SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterEscaped_macro_definition_body_alt2(this);
}

void SV3_1aPpParser::Escaped_macro_definition_body_alt2Context::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitEscaped_macro_definition_body_alt2(this);
}

SV3_1aPpParser::Escaped_macro_definition_body_alt2Context* SV3_1aPpParser::escaped_macro_definition_body_alt2() {
  Escaped_macro_definition_body_alt2Context *_localctx = _tracker.createInstance<Escaped_macro_definition_body_alt2Context>(_ctx, getState());
  enterRule(_localctx, 180, SV3_1aPpParser::RuleEscaped_macro_definition_body_alt2);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    size_t alt;
    enterOuterAlt(_localctx, 1);
    setState(942);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 62, _ctx);
    while (alt != 1 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1 + 1) {
        setState(940);
        _errHandler->sync(this);
        switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 61, _ctx)) {
        case 1: {
          setState(911);
          unterminated_string();
          break;
        }

        case 2: {
          setState(912);
          match(SV3_1aPpParser::Macro_identifier);
          break;
        }

        case 3: {
          setState(913);
          match(SV3_1aPpParser::Macro_Escaped_identifier);
          break;
        }

        case 4: {
          setState(914);
          escaped_identifier();
          break;
        }

        case 5: {
          setState(915);
          match(SV3_1aPpParser::Simple_identifier);
          break;
        }

        case 6: {
          setState(916);
          number();
          break;
        }

        case 7: {
          setState(917);
          match(SV3_1aPpParser::TEXT_CR);
          break;
        }

        case 8: {
          setState(918);
          pound_delay();
          break;
        }

        case 9: {
          setState(919);
          pound_pound_delay();
          break;
        }

        case 10: {
          setState(920);
          match(SV3_1aPpParser::ESCAPED_CR);
          break;
        }

        case 11: {
          setState(921);
          match(SV3_1aPpParser::PARENS_OPEN);
          break;
        }

        case 12: {
          setState(922);
          match(SV3_1aPpParser::PARENS_CLOSE);
          break;
        }

        case 13: {
          setState(923);
          match(SV3_1aPpParser::COMMA);
          break;
        }

        case 14: {
          setState(924);
          match(SV3_1aPpParser::EQUAL_OP);
          break;
        }

        case 15: {
          setState(925);
          match(SV3_1aPpParser::DOUBLE_QUOTE);
          break;
        }

        case 16: {
          setState(926);
          match(SV3_1aPpParser::TICK_VARIABLE);
          break;
        }

        case 17: {
          setState(927);
          directive_in_macro();
          break;
        }

        case 18: {
          setState(928);
          match(SV3_1aPpParser::Spaces);
          break;
        }

        case 19: {
          setState(929);
          match(SV3_1aPpParser::Fixed_point_number);
          break;
        }

        case 20: {
          setState(930);
          match(SV3_1aPpParser::String);
          break;
        }

        case 21: {
          setState(931);
          comments();
          break;
        }

        case 22: {
          setState(932);
          match(SV3_1aPpParser::TICK_QUOTE);
          break;
        }

        case 23: {
          setState(933);
          match(SV3_1aPpParser::TICK_BACKSLASH_TICK_QUOTE);
          break;
        }

        case 24: {
          setState(934);
          match(SV3_1aPpParser::TICK_TICK);
          break;
        }

        case 25: {
          setState(935);
          match(SV3_1aPpParser::Special);
          break;
        }

        case 26: {
          setState(936);
          match(SV3_1aPpParser::CURLY_OPEN);
          break;
        }

        case 27: {
          setState(937);
          match(SV3_1aPpParser::CURLY_CLOSE);
          break;
        }

        case 28: {
          setState(938);
          match(SV3_1aPpParser::SQUARE_OPEN);
          break;
        }

        case 29: {
          setState(939);
          match(SV3_1aPpParser::SQUARE_CLOSE);
          break;
        }

        default:
          break;
        } 
      }
      setState(944);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 62, _ctx);
    }
    setState(953);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case SV3_1aPpParser::CR: {
        setState(945);
        match(SV3_1aPpParser::CR);
        setState(949);
        _errHandler->sync(this);
        alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 63, _ctx);
        while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
          if (alt == 1) {
            setState(946);
            match(SV3_1aPpParser::Spaces); 
          }
          setState(951);
          _errHandler->sync(this);
          alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 63, _ctx);
        }
        break;
      }

      case SV3_1aPpParser::EOF: {
        setState(952);
        match(SV3_1aPpParser::EOF);
        break;
      }

    default:
      throw NoViableAltException(this);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Simple_macro_definition_bodyContext ------------------------------------------------------------------

SV3_1aPpParser::Simple_macro_definition_bodyContext::Simple_macro_definition_bodyContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<SV3_1aPpParser::Unterminated_stringContext *> SV3_1aPpParser::Simple_macro_definition_bodyContext::unterminated_string() {
  return getRuleContexts<SV3_1aPpParser::Unterminated_stringContext>();
}

SV3_1aPpParser::Unterminated_stringContext* SV3_1aPpParser::Simple_macro_definition_bodyContext::unterminated_string(size_t i) {
  return getRuleContext<SV3_1aPpParser::Unterminated_stringContext>(i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_bodyContext::Macro_identifier() {
  return getTokens(SV3_1aPpParser::Macro_identifier);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_bodyContext::Macro_identifier(size_t i) {
  return getToken(SV3_1aPpParser::Macro_identifier, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_bodyContext::Macro_Escaped_identifier() {
  return getTokens(SV3_1aPpParser::Macro_Escaped_identifier);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_bodyContext::Macro_Escaped_identifier(size_t i) {
  return getToken(SV3_1aPpParser::Macro_Escaped_identifier, i);
}

std::vector<SV3_1aPpParser::Escaped_identifierContext *> SV3_1aPpParser::Simple_macro_definition_bodyContext::escaped_identifier() {
  return getRuleContexts<SV3_1aPpParser::Escaped_identifierContext>();
}

SV3_1aPpParser::Escaped_identifierContext* SV3_1aPpParser::Simple_macro_definition_bodyContext::escaped_identifier(size_t i) {
  return getRuleContext<SV3_1aPpParser::Escaped_identifierContext>(i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_bodyContext::Simple_identifier() {
  return getTokens(SV3_1aPpParser::Simple_identifier);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_bodyContext::Simple_identifier(size_t i) {
  return getToken(SV3_1aPpParser::Simple_identifier, i);
}

std::vector<SV3_1aPpParser::NumberContext *> SV3_1aPpParser::Simple_macro_definition_bodyContext::number() {
  return getRuleContexts<SV3_1aPpParser::NumberContext>();
}

SV3_1aPpParser::NumberContext* SV3_1aPpParser::Simple_macro_definition_bodyContext::number(size_t i) {
  return getRuleContext<SV3_1aPpParser::NumberContext>(i);
}

std::vector<SV3_1aPpParser::Pound_delayContext *> SV3_1aPpParser::Simple_macro_definition_bodyContext::pound_delay() {
  return getRuleContexts<SV3_1aPpParser::Pound_delayContext>();
}

SV3_1aPpParser::Pound_delayContext* SV3_1aPpParser::Simple_macro_definition_bodyContext::pound_delay(size_t i) {
  return getRuleContext<SV3_1aPpParser::Pound_delayContext>(i);
}

std::vector<SV3_1aPpParser::Pound_pound_delayContext *> SV3_1aPpParser::Simple_macro_definition_bodyContext::pound_pound_delay() {
  return getRuleContexts<SV3_1aPpParser::Pound_pound_delayContext>();
}

SV3_1aPpParser::Pound_pound_delayContext* SV3_1aPpParser::Simple_macro_definition_bodyContext::pound_pound_delay(size_t i) {
  return getRuleContext<SV3_1aPpParser::Pound_pound_delayContext>(i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_bodyContext::TEXT_CR() {
  return getTokens(SV3_1aPpParser::TEXT_CR);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_bodyContext::TEXT_CR(size_t i) {
  return getToken(SV3_1aPpParser::TEXT_CR, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_bodyContext::PARENS_OPEN() {
  return getTokens(SV3_1aPpParser::PARENS_OPEN);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_bodyContext::PARENS_OPEN(size_t i) {
  return getToken(SV3_1aPpParser::PARENS_OPEN, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_bodyContext::PARENS_CLOSE() {
  return getTokens(SV3_1aPpParser::PARENS_CLOSE);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_bodyContext::PARENS_CLOSE(size_t i) {
  return getToken(SV3_1aPpParser::PARENS_CLOSE, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_bodyContext::COMMA() {
  return getTokens(SV3_1aPpParser::COMMA);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_bodyContext::COMMA(size_t i) {
  return getToken(SV3_1aPpParser::COMMA, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_bodyContext::EQUAL_OP() {
  return getTokens(SV3_1aPpParser::EQUAL_OP);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_bodyContext::EQUAL_OP(size_t i) {
  return getToken(SV3_1aPpParser::EQUAL_OP, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_bodyContext::DOUBLE_QUOTE() {
  return getTokens(SV3_1aPpParser::DOUBLE_QUOTE);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_bodyContext::DOUBLE_QUOTE(size_t i) {
  return getToken(SV3_1aPpParser::DOUBLE_QUOTE, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_bodyContext::TICK_VARIABLE() {
  return getTokens(SV3_1aPpParser::TICK_VARIABLE);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_bodyContext::TICK_VARIABLE(size_t i) {
  return getToken(SV3_1aPpParser::TICK_VARIABLE, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_bodyContext::Spaces() {
  return getTokens(SV3_1aPpParser::Spaces);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_bodyContext::Spaces(size_t i) {
  return getToken(SV3_1aPpParser::Spaces, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_bodyContext::Fixed_point_number() {
  return getTokens(SV3_1aPpParser::Fixed_point_number);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_bodyContext::Fixed_point_number(size_t i) {
  return getToken(SV3_1aPpParser::Fixed_point_number, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_bodyContext::String() {
  return getTokens(SV3_1aPpParser::String);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_bodyContext::String(size_t i) {
  return getToken(SV3_1aPpParser::String, i);
}

std::vector<SV3_1aPpParser::CommentsContext *> SV3_1aPpParser::Simple_macro_definition_bodyContext::comments() {
  return getRuleContexts<SV3_1aPpParser::CommentsContext>();
}

SV3_1aPpParser::CommentsContext* SV3_1aPpParser::Simple_macro_definition_bodyContext::comments(size_t i) {
  return getRuleContext<SV3_1aPpParser::CommentsContext>(i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_bodyContext::TICK_QUOTE() {
  return getTokens(SV3_1aPpParser::TICK_QUOTE);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_bodyContext::TICK_QUOTE(size_t i) {
  return getToken(SV3_1aPpParser::TICK_QUOTE, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_bodyContext::TICK_BACKSLASH_TICK_QUOTE() {
  return getTokens(SV3_1aPpParser::TICK_BACKSLASH_TICK_QUOTE);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_bodyContext::TICK_BACKSLASH_TICK_QUOTE(size_t i) {
  return getToken(SV3_1aPpParser::TICK_BACKSLASH_TICK_QUOTE, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_bodyContext::TICK_TICK() {
  return getTokens(SV3_1aPpParser::TICK_TICK);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_bodyContext::TICK_TICK(size_t i) {
  return getToken(SV3_1aPpParser::TICK_TICK, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_bodyContext::Special() {
  return getTokens(SV3_1aPpParser::Special);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_bodyContext::Special(size_t i) {
  return getToken(SV3_1aPpParser::Special, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_bodyContext::CURLY_OPEN() {
  return getTokens(SV3_1aPpParser::CURLY_OPEN);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_bodyContext::CURLY_OPEN(size_t i) {
  return getToken(SV3_1aPpParser::CURLY_OPEN, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_bodyContext::CURLY_CLOSE() {
  return getTokens(SV3_1aPpParser::CURLY_CLOSE);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_bodyContext::CURLY_CLOSE(size_t i) {
  return getToken(SV3_1aPpParser::CURLY_CLOSE, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_bodyContext::SQUARE_OPEN() {
  return getTokens(SV3_1aPpParser::SQUARE_OPEN);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_bodyContext::SQUARE_OPEN(size_t i) {
  return getToken(SV3_1aPpParser::SQUARE_OPEN, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_bodyContext::SQUARE_CLOSE() {
  return getTokens(SV3_1aPpParser::SQUARE_CLOSE);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_bodyContext::SQUARE_CLOSE(size_t i) {
  return getToken(SV3_1aPpParser::SQUARE_CLOSE, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_bodyContext::TICK_INCLUDE() {
  return getTokens(SV3_1aPpParser::TICK_INCLUDE);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_bodyContext::TICK_INCLUDE(size_t i) {
  return getToken(SV3_1aPpParser::TICK_INCLUDE, i);
}

std::vector<SV3_1aPpParser::Directive_in_macroContext *> SV3_1aPpParser::Simple_macro_definition_bodyContext::directive_in_macro() {
  return getRuleContexts<SV3_1aPpParser::Directive_in_macroContext>();
}

SV3_1aPpParser::Directive_in_macroContext* SV3_1aPpParser::Simple_macro_definition_bodyContext::directive_in_macro(size_t i) {
  return getRuleContext<SV3_1aPpParser::Directive_in_macroContext>(i);
}


size_t SV3_1aPpParser::Simple_macro_definition_bodyContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleSimple_macro_definition_body;
}

void SV3_1aPpParser::Simple_macro_definition_bodyContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterSimple_macro_definition_body(this);
}

void SV3_1aPpParser::Simple_macro_definition_bodyContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitSimple_macro_definition_body(this);
}

SV3_1aPpParser::Simple_macro_definition_bodyContext* SV3_1aPpParser::simple_macro_definition_body() {
  Simple_macro_definition_bodyContext *_localctx = _tracker.createInstance<Simple_macro_definition_bodyContext>(_ctx, getState());
  enterRule(_localctx, 182, SV3_1aPpParser::RuleSimple_macro_definition_body);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    size_t alt;
    enterOuterAlt(_localctx, 1);
    setState(986);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 66, _ctx);
    while (alt != 1 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1 + 1) {
        setState(984);
        _errHandler->sync(this);
        switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 65, _ctx)) {
        case 1: {
          setState(955);
          unterminated_string();
          break;
        }

        case 2: {
          setState(956);
          match(SV3_1aPpParser::Macro_identifier);
          break;
        }

        case 3: {
          setState(957);
          match(SV3_1aPpParser::Macro_Escaped_identifier);
          break;
        }

        case 4: {
          setState(958);
          escaped_identifier();
          break;
        }

        case 5: {
          setState(959);
          match(SV3_1aPpParser::Simple_identifier);
          break;
        }

        case 6: {
          setState(960);
          number();
          break;
        }

        case 7: {
          setState(961);
          pound_delay();
          break;
        }

        case 8: {
          setState(962);
          pound_pound_delay();
          break;
        }

        case 9: {
          setState(963);
          match(SV3_1aPpParser::TEXT_CR);
          break;
        }

        case 10: {
          setState(964);
          match(SV3_1aPpParser::PARENS_OPEN);
          break;
        }

        case 11: {
          setState(965);
          match(SV3_1aPpParser::PARENS_CLOSE);
          break;
        }

        case 12: {
          setState(966);
          match(SV3_1aPpParser::COMMA);
          break;
        }

        case 13: {
          setState(967);
          match(SV3_1aPpParser::EQUAL_OP);
          break;
        }

        case 14: {
          setState(968);
          match(SV3_1aPpParser::DOUBLE_QUOTE);
          break;
        }

        case 15: {
          setState(969);
          match(SV3_1aPpParser::TICK_VARIABLE);
          break;
        }

        case 16: {
          setState(970);
          match(SV3_1aPpParser::Spaces);
          break;
        }

        case 17: {
          setState(971);
          match(SV3_1aPpParser::Fixed_point_number);
          break;
        }

        case 18: {
          setState(972);
          match(SV3_1aPpParser::String);
          break;
        }

        case 19: {
          setState(973);
          comments();
          break;
        }

        case 20: {
          setState(974);
          match(SV3_1aPpParser::TICK_QUOTE);
          break;
        }

        case 21: {
          setState(975);
          match(SV3_1aPpParser::TICK_BACKSLASH_TICK_QUOTE);
          break;
        }

        case 22: {
          setState(976);
          match(SV3_1aPpParser::TICK_TICK);
          break;
        }

        case 23: {
          setState(977);
          match(SV3_1aPpParser::Special);
          break;
        }

        case 24: {
          setState(978);
          match(SV3_1aPpParser::CURLY_OPEN);
          break;
        }

        case 25: {
          setState(979);
          match(SV3_1aPpParser::CURLY_CLOSE);
          break;
        }

        case 26: {
          setState(980);
          match(SV3_1aPpParser::SQUARE_OPEN);
          break;
        }

        case 27: {
          setState(981);
          match(SV3_1aPpParser::SQUARE_CLOSE);
          break;
        }

        case 28: {
          setState(982);
          match(SV3_1aPpParser::TICK_INCLUDE);
          break;
        }

        case 29: {
          setState(983);
          directive_in_macro();
          break;
        }

        default:
          break;
        } 
      }
      setState(988);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 66, _ctx);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Simple_macro_definition_body_in_macro_bodyContext ------------------------------------------------------------------

SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::Simple_macro_definition_body_in_macro_bodyContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<SV3_1aPpParser::Unterminated_stringContext *> SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::unterminated_string() {
  return getRuleContexts<SV3_1aPpParser::Unterminated_stringContext>();
}

SV3_1aPpParser::Unterminated_stringContext* SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::unterminated_string(size_t i) {
  return getRuleContext<SV3_1aPpParser::Unterminated_stringContext>(i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::Macro_identifier() {
  return getTokens(SV3_1aPpParser::Macro_identifier);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::Macro_identifier(size_t i) {
  return getToken(SV3_1aPpParser::Macro_identifier, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::Macro_Escaped_identifier() {
  return getTokens(SV3_1aPpParser::Macro_Escaped_identifier);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::Macro_Escaped_identifier(size_t i) {
  return getToken(SV3_1aPpParser::Macro_Escaped_identifier, i);
}

std::vector<SV3_1aPpParser::Escaped_identifierContext *> SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::escaped_identifier() {
  return getRuleContexts<SV3_1aPpParser::Escaped_identifierContext>();
}

SV3_1aPpParser::Escaped_identifierContext* SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::escaped_identifier(size_t i) {
  return getRuleContext<SV3_1aPpParser::Escaped_identifierContext>(i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::Simple_identifier() {
  return getTokens(SV3_1aPpParser::Simple_identifier);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::Simple_identifier(size_t i) {
  return getToken(SV3_1aPpParser::Simple_identifier, i);
}

std::vector<SV3_1aPpParser::NumberContext *> SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::number() {
  return getRuleContexts<SV3_1aPpParser::NumberContext>();
}

SV3_1aPpParser::NumberContext* SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::number(size_t i) {
  return getRuleContext<SV3_1aPpParser::NumberContext>(i);
}

std::vector<SV3_1aPpParser::Pound_delayContext *> SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::pound_delay() {
  return getRuleContexts<SV3_1aPpParser::Pound_delayContext>();
}

SV3_1aPpParser::Pound_delayContext* SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::pound_delay(size_t i) {
  return getRuleContext<SV3_1aPpParser::Pound_delayContext>(i);
}

std::vector<SV3_1aPpParser::Pound_pound_delayContext *> SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::pound_pound_delay() {
  return getRuleContexts<SV3_1aPpParser::Pound_pound_delayContext>();
}

SV3_1aPpParser::Pound_pound_delayContext* SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::pound_pound_delay(size_t i) {
  return getRuleContext<SV3_1aPpParser::Pound_pound_delayContext>(i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::TEXT_CR() {
  return getTokens(SV3_1aPpParser::TEXT_CR);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::TEXT_CR(size_t i) {
  return getToken(SV3_1aPpParser::TEXT_CR, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::PARENS_OPEN() {
  return getTokens(SV3_1aPpParser::PARENS_OPEN);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::PARENS_OPEN(size_t i) {
  return getToken(SV3_1aPpParser::PARENS_OPEN, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::PARENS_CLOSE() {
  return getTokens(SV3_1aPpParser::PARENS_CLOSE);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::PARENS_CLOSE(size_t i) {
  return getToken(SV3_1aPpParser::PARENS_CLOSE, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::COMMA() {
  return getTokens(SV3_1aPpParser::COMMA);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::COMMA(size_t i) {
  return getToken(SV3_1aPpParser::COMMA, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::EQUAL_OP() {
  return getTokens(SV3_1aPpParser::EQUAL_OP);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::EQUAL_OP(size_t i) {
  return getToken(SV3_1aPpParser::EQUAL_OP, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::DOUBLE_QUOTE() {
  return getTokens(SV3_1aPpParser::DOUBLE_QUOTE);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::DOUBLE_QUOTE(size_t i) {
  return getToken(SV3_1aPpParser::DOUBLE_QUOTE, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::TICK_VARIABLE() {
  return getTokens(SV3_1aPpParser::TICK_VARIABLE);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::TICK_VARIABLE(size_t i) {
  return getToken(SV3_1aPpParser::TICK_VARIABLE, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::Spaces() {
  return getTokens(SV3_1aPpParser::Spaces);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::Spaces(size_t i) {
  return getToken(SV3_1aPpParser::Spaces, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::Fixed_point_number() {
  return getTokens(SV3_1aPpParser::Fixed_point_number);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::Fixed_point_number(size_t i) {
  return getToken(SV3_1aPpParser::Fixed_point_number, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::String() {
  return getTokens(SV3_1aPpParser::String);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::String(size_t i) {
  return getToken(SV3_1aPpParser::String, i);
}

std::vector<SV3_1aPpParser::CommentsContext *> SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::comments() {
  return getRuleContexts<SV3_1aPpParser::CommentsContext>();
}

SV3_1aPpParser::CommentsContext* SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::comments(size_t i) {
  return getRuleContext<SV3_1aPpParser::CommentsContext>(i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::TICK_QUOTE() {
  return getTokens(SV3_1aPpParser::TICK_QUOTE);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::TICK_QUOTE(size_t i) {
  return getToken(SV3_1aPpParser::TICK_QUOTE, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::TICK_BACKSLASH_TICK_QUOTE() {
  return getTokens(SV3_1aPpParser::TICK_BACKSLASH_TICK_QUOTE);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::TICK_BACKSLASH_TICK_QUOTE(size_t i) {
  return getToken(SV3_1aPpParser::TICK_BACKSLASH_TICK_QUOTE, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::TICK_TICK() {
  return getTokens(SV3_1aPpParser::TICK_TICK);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::TICK_TICK(size_t i) {
  return getToken(SV3_1aPpParser::TICK_TICK, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::Special() {
  return getTokens(SV3_1aPpParser::Special);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::Special(size_t i) {
  return getToken(SV3_1aPpParser::Special, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::CURLY_OPEN() {
  return getTokens(SV3_1aPpParser::CURLY_OPEN);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::CURLY_OPEN(size_t i) {
  return getToken(SV3_1aPpParser::CURLY_OPEN, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::CURLY_CLOSE() {
  return getTokens(SV3_1aPpParser::CURLY_CLOSE);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::CURLY_CLOSE(size_t i) {
  return getToken(SV3_1aPpParser::CURLY_CLOSE, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::SQUARE_OPEN() {
  return getTokens(SV3_1aPpParser::SQUARE_OPEN);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::SQUARE_OPEN(size_t i) {
  return getToken(SV3_1aPpParser::SQUARE_OPEN, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::SQUARE_CLOSE() {
  return getTokens(SV3_1aPpParser::SQUARE_CLOSE);
}

tree::TerminalNode* SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::SQUARE_CLOSE(size_t i) {
  return getToken(SV3_1aPpParser::SQUARE_CLOSE, i);
}


size_t SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleSimple_macro_definition_body_in_macro_body;
}

void SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterSimple_macro_definition_body_in_macro_body(this);
}

void SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitSimple_macro_definition_body_in_macro_body(this);
}

SV3_1aPpParser::Simple_macro_definition_body_in_macro_bodyContext* SV3_1aPpParser::simple_macro_definition_body_in_macro_body() {
  Simple_macro_definition_body_in_macro_bodyContext *_localctx = _tracker.createInstance<Simple_macro_definition_body_in_macro_bodyContext>(_ctx, getState());
  enterRule(_localctx, 184, SV3_1aPpParser::RuleSimple_macro_definition_body_in_macro_body);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    size_t alt;
    enterOuterAlt(_localctx, 1);
    setState(1018);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 68, _ctx);
    while (alt != 1 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1 + 1) {
        setState(1016);
        _errHandler->sync(this);
        switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 67, _ctx)) {
        case 1: {
          setState(989);
          unterminated_string();
          break;
        }

        case 2: {
          setState(990);
          match(SV3_1aPpParser::Macro_identifier);
          break;
        }

        case 3: {
          setState(991);
          match(SV3_1aPpParser::Macro_Escaped_identifier);
          break;
        }

        case 4: {
          setState(992);
          escaped_identifier();
          break;
        }

        case 5: {
          setState(993);
          match(SV3_1aPpParser::Simple_identifier);
          break;
        }

        case 6: {
          setState(994);
          number();
          break;
        }

        case 7: {
          setState(995);
          pound_delay();
          break;
        }

        case 8: {
          setState(996);
          pound_pound_delay();
          break;
        }

        case 9: {
          setState(997);
          match(SV3_1aPpParser::TEXT_CR);
          break;
        }

        case 10: {
          setState(998);
          match(SV3_1aPpParser::PARENS_OPEN);
          break;
        }

        case 11: {
          setState(999);
          match(SV3_1aPpParser::PARENS_CLOSE);
          break;
        }

        case 12: {
          setState(1000);
          match(SV3_1aPpParser::COMMA);
          break;
        }

        case 13: {
          setState(1001);
          match(SV3_1aPpParser::EQUAL_OP);
          break;
        }

        case 14: {
          setState(1002);
          match(SV3_1aPpParser::DOUBLE_QUOTE);
          break;
        }

        case 15: {
          setState(1003);
          match(SV3_1aPpParser::TICK_VARIABLE);
          break;
        }

        case 16: {
          setState(1004);
          match(SV3_1aPpParser::Spaces);
          break;
        }

        case 17: {
          setState(1005);
          match(SV3_1aPpParser::Fixed_point_number);
          break;
        }

        case 18: {
          setState(1006);
          match(SV3_1aPpParser::String);
          break;
        }

        case 19: {
          setState(1007);
          comments();
          break;
        }

        case 20: {
          setState(1008);
          match(SV3_1aPpParser::TICK_QUOTE);
          break;
        }

        case 21: {
          setState(1009);
          match(SV3_1aPpParser::TICK_BACKSLASH_TICK_QUOTE);
          break;
        }

        case 22: {
          setState(1010);
          match(SV3_1aPpParser::TICK_TICK);
          break;
        }

        case 23: {
          setState(1011);
          match(SV3_1aPpParser::Special);
          break;
        }

        case 24: {
          setState(1012);
          match(SV3_1aPpParser::CURLY_OPEN);
          break;
        }

        case 25: {
          setState(1013);
          match(SV3_1aPpParser::CURLY_CLOSE);
          break;
        }

        case 26: {
          setState(1014);
          match(SV3_1aPpParser::SQUARE_OPEN);
          break;
        }

        case 27: {
          setState(1015);
          match(SV3_1aPpParser::SQUARE_CLOSE);
          break;
        }

        default:
          break;
        } 
      }
      setState(1020);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 68, _ctx);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Pragma_expressionContext ------------------------------------------------------------------

SV3_1aPpParser::Pragma_expressionContext::Pragma_expressionContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Pragma_expressionContext::Simple_identifier() {
  return getToken(SV3_1aPpParser::Simple_identifier, 0);
}

SV3_1aPpParser::NumberContext* SV3_1aPpParser::Pragma_expressionContext::number() {
  return getRuleContext<SV3_1aPpParser::NumberContext>(0);
}

tree::TerminalNode* SV3_1aPpParser::Pragma_expressionContext::Spaces() {
  return getToken(SV3_1aPpParser::Spaces, 0);
}

tree::TerminalNode* SV3_1aPpParser::Pragma_expressionContext::Fixed_point_number() {
  return getToken(SV3_1aPpParser::Fixed_point_number, 0);
}

tree::TerminalNode* SV3_1aPpParser::Pragma_expressionContext::String() {
  return getToken(SV3_1aPpParser::String, 0);
}

tree::TerminalNode* SV3_1aPpParser::Pragma_expressionContext::CURLY_OPEN() {
  return getToken(SV3_1aPpParser::CURLY_OPEN, 0);
}

tree::TerminalNode* SV3_1aPpParser::Pragma_expressionContext::CURLY_CLOSE() {
  return getToken(SV3_1aPpParser::CURLY_CLOSE, 0);
}

tree::TerminalNode* SV3_1aPpParser::Pragma_expressionContext::SQUARE_OPEN() {
  return getToken(SV3_1aPpParser::SQUARE_OPEN, 0);
}

tree::TerminalNode* SV3_1aPpParser::Pragma_expressionContext::SQUARE_CLOSE() {
  return getToken(SV3_1aPpParser::SQUARE_CLOSE, 0);
}

tree::TerminalNode* SV3_1aPpParser::Pragma_expressionContext::PARENS_OPEN() {
  return getToken(SV3_1aPpParser::PARENS_OPEN, 0);
}

tree::TerminalNode* SV3_1aPpParser::Pragma_expressionContext::PARENS_CLOSE() {
  return getToken(SV3_1aPpParser::PARENS_CLOSE, 0);
}

tree::TerminalNode* SV3_1aPpParser::Pragma_expressionContext::COMMA() {
  return getToken(SV3_1aPpParser::COMMA, 0);
}

tree::TerminalNode* SV3_1aPpParser::Pragma_expressionContext::EQUAL_OP() {
  return getToken(SV3_1aPpParser::EQUAL_OP, 0);
}

tree::TerminalNode* SV3_1aPpParser::Pragma_expressionContext::DOUBLE_QUOTE() {
  return getToken(SV3_1aPpParser::DOUBLE_QUOTE, 0);
}

SV3_1aPpParser::Escaped_identifierContext* SV3_1aPpParser::Pragma_expressionContext::escaped_identifier() {
  return getRuleContext<SV3_1aPpParser::Escaped_identifierContext>(0);
}

SV3_1aPpParser::Pound_delayContext* SV3_1aPpParser::Pragma_expressionContext::pound_delay() {
  return getRuleContext<SV3_1aPpParser::Pound_delayContext>(0);
}

SV3_1aPpParser::Pound_pound_delayContext* SV3_1aPpParser::Pragma_expressionContext::pound_pound_delay() {
  return getRuleContext<SV3_1aPpParser::Pound_pound_delayContext>(0);
}

tree::TerminalNode* SV3_1aPpParser::Pragma_expressionContext::Special() {
  return getToken(SV3_1aPpParser::Special, 0);
}

tree::TerminalNode* SV3_1aPpParser::Pragma_expressionContext::ANY() {
  return getToken(SV3_1aPpParser::ANY, 0);
}


size_t SV3_1aPpParser::Pragma_expressionContext::getRuleIndex() const {
  return SV3_1aPpParser::RulePragma_expression;
}

void SV3_1aPpParser::Pragma_expressionContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterPragma_expression(this);
}

void SV3_1aPpParser::Pragma_expressionContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitPragma_expression(this);
}

SV3_1aPpParser::Pragma_expressionContext* SV3_1aPpParser::pragma_expression() {
  Pragma_expressionContext *_localctx = _tracker.createInstance<Pragma_expressionContext>(_ctx, getState());
  enterRule(_localctx, 186, SV3_1aPpParser::RulePragma_expression);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    setState(1040);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case SV3_1aPpParser::Simple_identifier: {
        enterOuterAlt(_localctx, 1);
        setState(1021);
        match(SV3_1aPpParser::Simple_identifier);
        break;
      }

      case SV3_1aPpParser::Number: {
        enterOuterAlt(_localctx, 2);
        setState(1022);
        number();
        break;
      }

      case SV3_1aPpParser::Spaces: {
        enterOuterAlt(_localctx, 3);
        setState(1023);
        match(SV3_1aPpParser::Spaces);
        break;
      }

      case SV3_1aPpParser::Fixed_point_number: {
        enterOuterAlt(_localctx, 4);
        setState(1024);
        match(SV3_1aPpParser::Fixed_point_number);
        break;
      }

      case SV3_1aPpParser::String: {
        enterOuterAlt(_localctx, 5);
        setState(1025);
        match(SV3_1aPpParser::String);
        break;
      }

      case SV3_1aPpParser::CURLY_OPEN: {
        enterOuterAlt(_localctx, 6);
        setState(1026);
        match(SV3_1aPpParser::CURLY_OPEN);
        break;
      }

      case SV3_1aPpParser::CURLY_CLOSE: {
        enterOuterAlt(_localctx, 7);
        setState(1027);
        match(SV3_1aPpParser::CURLY_CLOSE);
        break;
      }

      case SV3_1aPpParser::SQUARE_OPEN: {
        enterOuterAlt(_localctx, 8);
        setState(1028);
        match(SV3_1aPpParser::SQUARE_OPEN);
        break;
      }

      case SV3_1aPpParser::SQUARE_CLOSE: {
        enterOuterAlt(_localctx, 9);
        setState(1029);
        match(SV3_1aPpParser::SQUARE_CLOSE);
        break;
      }

      case SV3_1aPpParser::PARENS_OPEN: {
        enterOuterAlt(_localctx, 10);
        setState(1030);
        match(SV3_1aPpParser::PARENS_OPEN);
        break;
      }

      case SV3_1aPpParser::PARENS_CLOSE: {
        enterOuterAlt(_localctx, 11);
        setState(1031);
        match(SV3_1aPpParser::PARENS_CLOSE);
        break;
      }

      case SV3_1aPpParser::COMMA: {
        enterOuterAlt(_localctx, 12);
        setState(1032);
        match(SV3_1aPpParser::COMMA);
        break;
      }

      case SV3_1aPpParser::EQUAL_OP: {
        enterOuterAlt(_localctx, 13);
        setState(1033);
        match(SV3_1aPpParser::EQUAL_OP);
        break;
      }

      case SV3_1aPpParser::DOUBLE_QUOTE: {
        enterOuterAlt(_localctx, 14);
        setState(1034);
        match(SV3_1aPpParser::DOUBLE_QUOTE);
        break;
      }

      case SV3_1aPpParser::Escaped_identifier: {
        enterOuterAlt(_localctx, 15);
        setState(1035);
        escaped_identifier();
        break;
      }

      case SV3_1aPpParser::Pound_delay: {
        enterOuterAlt(_localctx, 16);
        setState(1036);
        pound_delay();
        break;
      }

      case SV3_1aPpParser::Pound_Pound_delay: {
        enterOuterAlt(_localctx, 17);
        setState(1037);
        pound_pound_delay();
        break;
      }

      case SV3_1aPpParser::Special: {
        enterOuterAlt(_localctx, 18);
        setState(1038);
        match(SV3_1aPpParser::Special);
        break;
      }

      case SV3_1aPpParser::ANY: {
        enterOuterAlt(_localctx, 19);
        setState(1039);
        match(SV3_1aPpParser::ANY);
        break;
      }

    default:
      throw NoViableAltException(this);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Macro_argContext ------------------------------------------------------------------

SV3_1aPpParser::Macro_argContext::Macro_argContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Macro_argContext::Simple_identifier() {
  return getToken(SV3_1aPpParser::Simple_identifier, 0);
}

SV3_1aPpParser::NumberContext* SV3_1aPpParser::Macro_argContext::number() {
  return getRuleContext<SV3_1aPpParser::NumberContext>(0);
}

tree::TerminalNode* SV3_1aPpParser::Macro_argContext::Spaces() {
  return getToken(SV3_1aPpParser::Spaces, 0);
}

tree::TerminalNode* SV3_1aPpParser::Macro_argContext::Fixed_point_number() {
  return getToken(SV3_1aPpParser::Fixed_point_number, 0);
}

tree::TerminalNode* SV3_1aPpParser::Macro_argContext::String() {
  return getToken(SV3_1aPpParser::String, 0);
}

SV3_1aPpParser::Paired_parensContext* SV3_1aPpParser::Macro_argContext::paired_parens() {
  return getRuleContext<SV3_1aPpParser::Paired_parensContext>(0);
}

tree::TerminalNode* SV3_1aPpParser::Macro_argContext::EQUAL_OP() {
  return getToken(SV3_1aPpParser::EQUAL_OP, 0);
}

tree::TerminalNode* SV3_1aPpParser::Macro_argContext::DOUBLE_QUOTE() {
  return getToken(SV3_1aPpParser::DOUBLE_QUOTE, 0);
}

SV3_1aPpParser::Macro_instanceContext* SV3_1aPpParser::Macro_argContext::macro_instance() {
  return getRuleContext<SV3_1aPpParser::Macro_instanceContext>(0);
}

tree::TerminalNode* SV3_1aPpParser::Macro_argContext::CR() {
  return getToken(SV3_1aPpParser::CR, 0);
}

tree::TerminalNode* SV3_1aPpParser::Macro_argContext::TEXT_CR() {
  return getToken(SV3_1aPpParser::TEXT_CR, 0);
}

SV3_1aPpParser::Escaped_identifierContext* SV3_1aPpParser::Macro_argContext::escaped_identifier() {
  return getRuleContext<SV3_1aPpParser::Escaped_identifierContext>(0);
}

SV3_1aPpParser::Simple_args_macro_definition_in_macro_bodyContext* SV3_1aPpParser::Macro_argContext::simple_args_macro_definition_in_macro_body() {
  return getRuleContext<SV3_1aPpParser::Simple_args_macro_definition_in_macro_bodyContext>(0);
}

SV3_1aPpParser::Simple_no_args_macro_definition_in_macro_bodyContext* SV3_1aPpParser::Macro_argContext::simple_no_args_macro_definition_in_macro_body() {
  return getRuleContext<SV3_1aPpParser::Simple_no_args_macro_definition_in_macro_bodyContext>(0);
}

SV3_1aPpParser::CommentsContext* SV3_1aPpParser::Macro_argContext::comments() {
  return getRuleContext<SV3_1aPpParser::CommentsContext>(0);
}

SV3_1aPpParser::Pound_delayContext* SV3_1aPpParser::Macro_argContext::pound_delay() {
  return getRuleContext<SV3_1aPpParser::Pound_delayContext>(0);
}

SV3_1aPpParser::Pound_pound_delayContext* SV3_1aPpParser::Macro_argContext::pound_pound_delay() {
  return getRuleContext<SV3_1aPpParser::Pound_pound_delayContext>(0);
}

tree::TerminalNode* SV3_1aPpParser::Macro_argContext::Special() {
  return getToken(SV3_1aPpParser::Special, 0);
}

tree::TerminalNode* SV3_1aPpParser::Macro_argContext::ANY() {
  return getToken(SV3_1aPpParser::ANY, 0);
}


size_t SV3_1aPpParser::Macro_argContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleMacro_arg;
}

void SV3_1aPpParser::Macro_argContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterMacro_arg(this);
}

void SV3_1aPpParser::Macro_argContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitMacro_arg(this);
}

SV3_1aPpParser::Macro_argContext* SV3_1aPpParser::macro_arg() {
  Macro_argContext *_localctx = _tracker.createInstance<Macro_argContext>(_ctx, getState());
  enterRule(_localctx, 188, SV3_1aPpParser::RuleMacro_arg);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    setState(1061);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 70, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(1042);
      match(SV3_1aPpParser::Simple_identifier);
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(1043);
      number();
      break;
    }

    case 3: {
      enterOuterAlt(_localctx, 3);
      setState(1044);
      match(SV3_1aPpParser::Spaces);
      break;
    }

    case 4: {
      enterOuterAlt(_localctx, 4);
      setState(1045);
      match(SV3_1aPpParser::Fixed_point_number);
      break;
    }

    case 5: {
      enterOuterAlt(_localctx, 5);
      setState(1046);
      match(SV3_1aPpParser::String);
      break;
    }

    case 6: {
      enterOuterAlt(_localctx, 6);
      setState(1047);
      paired_parens();
      break;
    }

    case 7: {
      enterOuterAlt(_localctx, 7);
      setState(1048);
      match(SV3_1aPpParser::EQUAL_OP);
      break;
    }

    case 8: {
      enterOuterAlt(_localctx, 8);
      setState(1049);
      match(SV3_1aPpParser::DOUBLE_QUOTE);
      break;
    }

    case 9: {
      enterOuterAlt(_localctx, 9);
      setState(1050);
      macro_instance();
      break;
    }

    case 10: {
      enterOuterAlt(_localctx, 10);
      setState(1051);
      match(SV3_1aPpParser::CR);
      break;
    }

    case 11: {
      enterOuterAlt(_localctx, 11);
      setState(1052);
      match(SV3_1aPpParser::TEXT_CR);
      break;
    }

    case 12: {
      enterOuterAlt(_localctx, 12);
      setState(1053);
      escaped_identifier();
      break;
    }

    case 13: {
      enterOuterAlt(_localctx, 13);
      setState(1054);
      simple_args_macro_definition_in_macro_body();
      break;
    }

    case 14: {
      enterOuterAlt(_localctx, 14);
      setState(1055);
      simple_no_args_macro_definition_in_macro_body();
      break;
    }

    case 15: {
      enterOuterAlt(_localctx, 15);
      setState(1056);
      comments();
      break;
    }

    case 16: {
      enterOuterAlt(_localctx, 16);
      setState(1057);
      pound_delay();
      break;
    }

    case 17: {
      enterOuterAlt(_localctx, 17);
      setState(1058);
      pound_pound_delay();
      break;
    }

    case 18: {
      enterOuterAlt(_localctx, 18);
      setState(1059);
      match(SV3_1aPpParser::Special);
      break;
    }

    case 19: {
      enterOuterAlt(_localctx, 19);
      setState(1060);
      match(SV3_1aPpParser::ANY);
      break;
    }

    default:
      break;
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Paired_parensContext ------------------------------------------------------------------

SV3_1aPpParser::Paired_parensContext::Paired_parensContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Paired_parensContext::PARENS_OPEN() {
  return getToken(SV3_1aPpParser::PARENS_OPEN, 0);
}

tree::TerminalNode* SV3_1aPpParser::Paired_parensContext::PARENS_CLOSE() {
  return getToken(SV3_1aPpParser::PARENS_CLOSE, 0);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Paired_parensContext::Simple_identifier() {
  return getTokens(SV3_1aPpParser::Simple_identifier);
}

tree::TerminalNode* SV3_1aPpParser::Paired_parensContext::Simple_identifier(size_t i) {
  return getToken(SV3_1aPpParser::Simple_identifier, i);
}

std::vector<SV3_1aPpParser::NumberContext *> SV3_1aPpParser::Paired_parensContext::number() {
  return getRuleContexts<SV3_1aPpParser::NumberContext>();
}

SV3_1aPpParser::NumberContext* SV3_1aPpParser::Paired_parensContext::number(size_t i) {
  return getRuleContext<SV3_1aPpParser::NumberContext>(i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Paired_parensContext::Spaces() {
  return getTokens(SV3_1aPpParser::Spaces);
}

tree::TerminalNode* SV3_1aPpParser::Paired_parensContext::Spaces(size_t i) {
  return getToken(SV3_1aPpParser::Spaces, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Paired_parensContext::Fixed_point_number() {
  return getTokens(SV3_1aPpParser::Fixed_point_number);
}

tree::TerminalNode* SV3_1aPpParser::Paired_parensContext::Fixed_point_number(size_t i) {
  return getToken(SV3_1aPpParser::Fixed_point_number, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Paired_parensContext::String() {
  return getTokens(SV3_1aPpParser::String);
}

tree::TerminalNode* SV3_1aPpParser::Paired_parensContext::String(size_t i) {
  return getToken(SV3_1aPpParser::String, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Paired_parensContext::COMMA() {
  return getTokens(SV3_1aPpParser::COMMA);
}

tree::TerminalNode* SV3_1aPpParser::Paired_parensContext::COMMA(size_t i) {
  return getToken(SV3_1aPpParser::COMMA, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Paired_parensContext::EQUAL_OP() {
  return getTokens(SV3_1aPpParser::EQUAL_OP);
}

tree::TerminalNode* SV3_1aPpParser::Paired_parensContext::EQUAL_OP(size_t i) {
  return getToken(SV3_1aPpParser::EQUAL_OP, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Paired_parensContext::DOUBLE_QUOTE() {
  return getTokens(SV3_1aPpParser::DOUBLE_QUOTE);
}

tree::TerminalNode* SV3_1aPpParser::Paired_parensContext::DOUBLE_QUOTE(size_t i) {
  return getToken(SV3_1aPpParser::DOUBLE_QUOTE, i);
}

std::vector<SV3_1aPpParser::Macro_instanceContext *> SV3_1aPpParser::Paired_parensContext::macro_instance() {
  return getRuleContexts<SV3_1aPpParser::Macro_instanceContext>();
}

SV3_1aPpParser::Macro_instanceContext* SV3_1aPpParser::Paired_parensContext::macro_instance(size_t i) {
  return getRuleContext<SV3_1aPpParser::Macro_instanceContext>(i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Paired_parensContext::TEXT_CR() {
  return getTokens(SV3_1aPpParser::TEXT_CR);
}

tree::TerminalNode* SV3_1aPpParser::Paired_parensContext::TEXT_CR(size_t i) {
  return getToken(SV3_1aPpParser::TEXT_CR, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Paired_parensContext::CR() {
  return getTokens(SV3_1aPpParser::CR);
}

tree::TerminalNode* SV3_1aPpParser::Paired_parensContext::CR(size_t i) {
  return getToken(SV3_1aPpParser::CR, i);
}

std::vector<SV3_1aPpParser::Paired_parensContext *> SV3_1aPpParser::Paired_parensContext::paired_parens() {
  return getRuleContexts<SV3_1aPpParser::Paired_parensContext>();
}

SV3_1aPpParser::Paired_parensContext* SV3_1aPpParser::Paired_parensContext::paired_parens(size_t i) {
  return getRuleContext<SV3_1aPpParser::Paired_parensContext>(i);
}

std::vector<SV3_1aPpParser::Escaped_identifierContext *> SV3_1aPpParser::Paired_parensContext::escaped_identifier() {
  return getRuleContexts<SV3_1aPpParser::Escaped_identifierContext>();
}

SV3_1aPpParser::Escaped_identifierContext* SV3_1aPpParser::Paired_parensContext::escaped_identifier(size_t i) {
  return getRuleContext<SV3_1aPpParser::Escaped_identifierContext>(i);
}

std::vector<SV3_1aPpParser::CommentsContext *> SV3_1aPpParser::Paired_parensContext::comments() {
  return getRuleContexts<SV3_1aPpParser::CommentsContext>();
}

SV3_1aPpParser::CommentsContext* SV3_1aPpParser::Paired_parensContext::comments(size_t i) {
  return getRuleContext<SV3_1aPpParser::CommentsContext>(i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Paired_parensContext::Special() {
  return getTokens(SV3_1aPpParser::Special);
}

tree::TerminalNode* SV3_1aPpParser::Paired_parensContext::Special(size_t i) {
  return getToken(SV3_1aPpParser::Special, i);
}

std::vector<tree::TerminalNode *> SV3_1aPpParser::Paired_parensContext::ANY() {
  return getTokens(SV3_1aPpParser::ANY);
}

tree::TerminalNode* SV3_1aPpParser::Paired_parensContext::ANY(size_t i) {
  return getToken(SV3_1aPpParser::ANY, i);
}

tree::TerminalNode* SV3_1aPpParser::Paired_parensContext::CURLY_OPEN() {
  return getToken(SV3_1aPpParser::CURLY_OPEN, 0);
}

tree::TerminalNode* SV3_1aPpParser::Paired_parensContext::CURLY_CLOSE() {
  return getToken(SV3_1aPpParser::CURLY_CLOSE, 0);
}

tree::TerminalNode* SV3_1aPpParser::Paired_parensContext::SQUARE_OPEN() {
  return getToken(SV3_1aPpParser::SQUARE_OPEN, 0);
}

tree::TerminalNode* SV3_1aPpParser::Paired_parensContext::SQUARE_CLOSE() {
  return getToken(SV3_1aPpParser::SQUARE_CLOSE, 0);
}


size_t SV3_1aPpParser::Paired_parensContext::getRuleIndex() const {
  return SV3_1aPpParser::RulePaired_parens;
}

void SV3_1aPpParser::Paired_parensContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterPaired_parens(this);
}

void SV3_1aPpParser::Paired_parensContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitPaired_parens(this);
}

SV3_1aPpParser::Paired_parensContext* SV3_1aPpParser::paired_parens() {
  Paired_parensContext *_localctx = _tracker.createInstance<Paired_parensContext>(_ctx, getState());
  enterRule(_localctx, 190, SV3_1aPpParser::RulePaired_parens);
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    setState(1130);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case SV3_1aPpParser::PARENS_OPEN: {
        enterOuterAlt(_localctx, 1);
        setState(1063);
        match(SV3_1aPpParser::PARENS_OPEN);
        setState(1082);
        _errHandler->sync(this);
        _la = _input->LA(1);
        while (_la == SV3_1aPpParser::One_line_comment

        || _la == SV3_1aPpParser::Block_comment || ((((_la - 67) & ~ 0x3fULL) == 0) &&
          ((1ULL << (_la - 67)) & ((1ULL << (SV3_1aPpParser::Macro_identifier - 67))
          | (1ULL << (SV3_1aPpParser::Macro_Escaped_identifier - 67))
          | (1ULL << (SV3_1aPpParser::String - 67))
          | (1ULL << (SV3_1aPpParser::Simple_identifier - 67))
          | (1ULL << (SV3_1aPpParser::Spaces - 67))
          | (1ULL << (SV3_1aPpParser::Number - 67))
          | (1ULL << (SV3_1aPpParser::Fixed_point_number - 67))
          | (1ULL << (SV3_1aPpParser::TEXT_CR - 67))
          | (1ULL << (SV3_1aPpParser::CR - 67))
          | (1ULL << (SV3_1aPpParser::PARENS_OPEN - 67))
          | (1ULL << (SV3_1aPpParser::COMMA - 67))
          | (1ULL << (SV3_1aPpParser::EQUAL_OP - 67))
          | (1ULL << (SV3_1aPpParser::DOUBLE_QUOTE - 67))
          | (1ULL << (SV3_1aPpParser::Escaped_identifier - 67))
          | (1ULL << (SV3_1aPpParser::CURLY_OPEN - 67))
          | (1ULL << (SV3_1aPpParser::SQUARE_OPEN - 67))
          | (1ULL << (SV3_1aPpParser::Special - 67))
          | (1ULL << (SV3_1aPpParser::ANY - 67)))) != 0)) {
          setState(1080);
          _errHandler->sync(this);
          switch (_input->LA(1)) {
            case SV3_1aPpParser::Simple_identifier: {
              setState(1064);
              match(SV3_1aPpParser::Simple_identifier);
              break;
            }

            case SV3_1aPpParser::Number: {
              setState(1065);
              number();
              break;
            }

            case SV3_1aPpParser::Spaces: {
              setState(1066);
              match(SV3_1aPpParser::Spaces);
              break;
            }

            case SV3_1aPpParser::Fixed_point_number: {
              setState(1067);
              match(SV3_1aPpParser::Fixed_point_number);
              break;
            }

            case SV3_1aPpParser::String: {
              setState(1068);
              match(SV3_1aPpParser::String);
              break;
            }

            case SV3_1aPpParser::COMMA: {
              setState(1069);
              match(SV3_1aPpParser::COMMA);
              break;
            }

            case SV3_1aPpParser::EQUAL_OP: {
              setState(1070);
              match(SV3_1aPpParser::EQUAL_OP);
              break;
            }

            case SV3_1aPpParser::DOUBLE_QUOTE: {
              setState(1071);
              match(SV3_1aPpParser::DOUBLE_QUOTE);
              break;
            }

            case SV3_1aPpParser::Macro_identifier:
            case SV3_1aPpParser::Macro_Escaped_identifier: {
              setState(1072);
              macro_instance();
              break;
            }

            case SV3_1aPpParser::TEXT_CR: {
              setState(1073);
              match(SV3_1aPpParser::TEXT_CR);
              break;
            }

            case SV3_1aPpParser::CR: {
              setState(1074);
              match(SV3_1aPpParser::CR);
              break;
            }

            case SV3_1aPpParser::PARENS_OPEN:
            case SV3_1aPpParser::CURLY_OPEN:
            case SV3_1aPpParser::SQUARE_OPEN: {
              setState(1075);
              paired_parens();
              break;
            }

            case SV3_1aPpParser::Escaped_identifier: {
              setState(1076);
              escaped_identifier();
              break;
            }

            case SV3_1aPpParser::One_line_comment:
            case SV3_1aPpParser::Block_comment: {
              setState(1077);
              comments();
              break;
            }

            case SV3_1aPpParser::Special: {
              setState(1078);
              match(SV3_1aPpParser::Special);
              break;
            }

            case SV3_1aPpParser::ANY: {
              setState(1079);
              match(SV3_1aPpParser::ANY);
              break;
            }

          default:
            throw NoViableAltException(this);
          }
          setState(1084);
          _errHandler->sync(this);
          _la = _input->LA(1);
        }
        setState(1085);
        match(SV3_1aPpParser::PARENS_CLOSE);
        break;
      }

      case SV3_1aPpParser::CURLY_OPEN: {
        enterOuterAlt(_localctx, 2);
        setState(1086);
        match(SV3_1aPpParser::CURLY_OPEN);
        setState(1104);
        _errHandler->sync(this);
        _la = _input->LA(1);
        while (_la == SV3_1aPpParser::One_line_comment

        || _la == SV3_1aPpParser::Block_comment || ((((_la - 67) & ~ 0x3fULL) == 0) &&
          ((1ULL << (_la - 67)) & ((1ULL << (SV3_1aPpParser::Macro_identifier - 67))
          | (1ULL << (SV3_1aPpParser::Macro_Escaped_identifier - 67))
          | (1ULL << (SV3_1aPpParser::String - 67))
          | (1ULL << (SV3_1aPpParser::Simple_identifier - 67))
          | (1ULL << (SV3_1aPpParser::Spaces - 67))
          | (1ULL << (SV3_1aPpParser::Number - 67))
          | (1ULL << (SV3_1aPpParser::Fixed_point_number - 67))
          | (1ULL << (SV3_1aPpParser::CR - 67))
          | (1ULL << (SV3_1aPpParser::PARENS_OPEN - 67))
          | (1ULL << (SV3_1aPpParser::COMMA - 67))
          | (1ULL << (SV3_1aPpParser::EQUAL_OP - 67))
          | (1ULL << (SV3_1aPpParser::DOUBLE_QUOTE - 67))
          | (1ULL << (SV3_1aPpParser::Escaped_identifier - 67))
          | (1ULL << (SV3_1aPpParser::CURLY_OPEN - 67))
          | (1ULL << (SV3_1aPpParser::SQUARE_OPEN - 67))
          | (1ULL << (SV3_1aPpParser::Special - 67))
          | (1ULL << (SV3_1aPpParser::ANY - 67)))) != 0)) {
          setState(1102);
          _errHandler->sync(this);
          switch (_input->LA(1)) {
            case SV3_1aPpParser::Simple_identifier: {
              setState(1087);
              match(SV3_1aPpParser::Simple_identifier);
              break;
            }

            case SV3_1aPpParser::Number: {
              setState(1088);
              number();
              break;
            }

            case SV3_1aPpParser::Spaces: {
              setState(1089);
              match(SV3_1aPpParser::Spaces);
              break;
            }

            case SV3_1aPpParser::Fixed_point_number: {
              setState(1090);
              match(SV3_1aPpParser::Fixed_point_number);
              break;
            }

            case SV3_1aPpParser::String: {
              setState(1091);
              match(SV3_1aPpParser::String);
              break;
            }

            case SV3_1aPpParser::COMMA: {
              setState(1092);
              match(SV3_1aPpParser::COMMA);
              break;
            }

            case SV3_1aPpParser::EQUAL_OP: {
              setState(1093);
              match(SV3_1aPpParser::EQUAL_OP);
              break;
            }

            case SV3_1aPpParser::DOUBLE_QUOTE: {
              setState(1094);
              match(SV3_1aPpParser::DOUBLE_QUOTE);
              break;
            }

            case SV3_1aPpParser::Macro_identifier:
            case SV3_1aPpParser::Macro_Escaped_identifier: {
              setState(1095);
              macro_instance();
              break;
            }

            case SV3_1aPpParser::CR: {
              setState(1096);
              match(SV3_1aPpParser::CR);
              break;
            }

            case SV3_1aPpParser::PARENS_OPEN:
            case SV3_1aPpParser::CURLY_OPEN:
            case SV3_1aPpParser::SQUARE_OPEN: {
              setState(1097);
              paired_parens();
              break;
            }

            case SV3_1aPpParser::Escaped_identifier: {
              setState(1098);
              escaped_identifier();
              break;
            }

            case SV3_1aPpParser::One_line_comment:
            case SV3_1aPpParser::Block_comment: {
              setState(1099);
              comments();
              break;
            }

            case SV3_1aPpParser::Special: {
              setState(1100);
              match(SV3_1aPpParser::Special);
              break;
            }

            case SV3_1aPpParser::ANY: {
              setState(1101);
              match(SV3_1aPpParser::ANY);
              break;
            }

          default:
            throw NoViableAltException(this);
          }
          setState(1106);
          _errHandler->sync(this);
          _la = _input->LA(1);
        }
        setState(1107);
        match(SV3_1aPpParser::CURLY_CLOSE);
        break;
      }

      case SV3_1aPpParser::SQUARE_OPEN: {
        enterOuterAlt(_localctx, 3);
        setState(1108);
        match(SV3_1aPpParser::SQUARE_OPEN);
        setState(1126);
        _errHandler->sync(this);
        _la = _input->LA(1);
        while (_la == SV3_1aPpParser::One_line_comment

        || _la == SV3_1aPpParser::Block_comment || ((((_la - 67) & ~ 0x3fULL) == 0) &&
          ((1ULL << (_la - 67)) & ((1ULL << (SV3_1aPpParser::Macro_identifier - 67))
          | (1ULL << (SV3_1aPpParser::Macro_Escaped_identifier - 67))
          | (1ULL << (SV3_1aPpParser::String - 67))
          | (1ULL << (SV3_1aPpParser::Simple_identifier - 67))
          | (1ULL << (SV3_1aPpParser::Spaces - 67))
          | (1ULL << (SV3_1aPpParser::Number - 67))
          | (1ULL << (SV3_1aPpParser::Fixed_point_number - 67))
          | (1ULL << (SV3_1aPpParser::CR - 67))
          | (1ULL << (SV3_1aPpParser::PARENS_OPEN - 67))
          | (1ULL << (SV3_1aPpParser::COMMA - 67))
          | (1ULL << (SV3_1aPpParser::EQUAL_OP - 67))
          | (1ULL << (SV3_1aPpParser::DOUBLE_QUOTE - 67))
          | (1ULL << (SV3_1aPpParser::Escaped_identifier - 67))
          | (1ULL << (SV3_1aPpParser::CURLY_OPEN - 67))
          | (1ULL << (SV3_1aPpParser::SQUARE_OPEN - 67))
          | (1ULL << (SV3_1aPpParser::Special - 67))
          | (1ULL << (SV3_1aPpParser::ANY - 67)))) != 0)) {
          setState(1124);
          _errHandler->sync(this);
          switch (_input->LA(1)) {
            case SV3_1aPpParser::Simple_identifier: {
              setState(1109);
              match(SV3_1aPpParser::Simple_identifier);
              break;
            }

            case SV3_1aPpParser::Number: {
              setState(1110);
              number();
              break;
            }

            case SV3_1aPpParser::Spaces: {
              setState(1111);
              match(SV3_1aPpParser::Spaces);
              break;
            }

            case SV3_1aPpParser::Fixed_point_number: {
              setState(1112);
              match(SV3_1aPpParser::Fixed_point_number);
              break;
            }

            case SV3_1aPpParser::String: {
              setState(1113);
              match(SV3_1aPpParser::String);
              break;
            }

            case SV3_1aPpParser::COMMA: {
              setState(1114);
              match(SV3_1aPpParser::COMMA);
              break;
            }

            case SV3_1aPpParser::EQUAL_OP: {
              setState(1115);
              match(SV3_1aPpParser::EQUAL_OP);
              break;
            }

            case SV3_1aPpParser::DOUBLE_QUOTE: {
              setState(1116);
              match(SV3_1aPpParser::DOUBLE_QUOTE);
              break;
            }

            case SV3_1aPpParser::Macro_identifier:
            case SV3_1aPpParser::Macro_Escaped_identifier: {
              setState(1117);
              macro_instance();
              break;
            }

            case SV3_1aPpParser::CR: {
              setState(1118);
              match(SV3_1aPpParser::CR);
              break;
            }

            case SV3_1aPpParser::PARENS_OPEN:
            case SV3_1aPpParser::CURLY_OPEN:
            case SV3_1aPpParser::SQUARE_OPEN: {
              setState(1119);
              paired_parens();
              break;
            }

            case SV3_1aPpParser::Escaped_identifier: {
              setState(1120);
              escaped_identifier();
              break;
            }

            case SV3_1aPpParser::One_line_comment:
            case SV3_1aPpParser::Block_comment: {
              setState(1121);
              comments();
              break;
            }

            case SV3_1aPpParser::Special: {
              setState(1122);
              match(SV3_1aPpParser::Special);
              break;
            }

            case SV3_1aPpParser::ANY: {
              setState(1123);
              match(SV3_1aPpParser::ANY);
              break;
            }

          default:
            throw NoViableAltException(this);
          }
          setState(1128);
          _errHandler->sync(this);
          _la = _input->LA(1);
        }
        setState(1129);
        match(SV3_1aPpParser::SQUARE_CLOSE);
        break;
      }

    default:
      throw NoViableAltException(this);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Text_blobContext ------------------------------------------------------------------

SV3_1aPpParser::Text_blobContext::Text_blobContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Text_blobContext::Simple_identifier() {
  return getToken(SV3_1aPpParser::Simple_identifier, 0);
}

SV3_1aPpParser::NumberContext* SV3_1aPpParser::Text_blobContext::number() {
  return getRuleContext<SV3_1aPpParser::NumberContext>(0);
}

tree::TerminalNode* SV3_1aPpParser::Text_blobContext::CR() {
  return getToken(SV3_1aPpParser::CR, 0);
}

tree::TerminalNode* SV3_1aPpParser::Text_blobContext::Spaces() {
  return getToken(SV3_1aPpParser::Spaces, 0);
}

tree::TerminalNode* SV3_1aPpParser::Text_blobContext::Fixed_point_number() {
  return getToken(SV3_1aPpParser::Fixed_point_number, 0);
}

tree::TerminalNode* SV3_1aPpParser::Text_blobContext::ESCAPED_CR() {
  return getToken(SV3_1aPpParser::ESCAPED_CR, 0);
}

tree::TerminalNode* SV3_1aPpParser::Text_blobContext::String() {
  return getToken(SV3_1aPpParser::String, 0);
}

tree::TerminalNode* SV3_1aPpParser::Text_blobContext::PARENS_OPEN() {
  return getToken(SV3_1aPpParser::PARENS_OPEN, 0);
}

tree::TerminalNode* SV3_1aPpParser::Text_blobContext::PARENS_CLOSE() {
  return getToken(SV3_1aPpParser::PARENS_CLOSE, 0);
}

tree::TerminalNode* SV3_1aPpParser::Text_blobContext::COMMA() {
  return getToken(SV3_1aPpParser::COMMA, 0);
}

tree::TerminalNode* SV3_1aPpParser::Text_blobContext::EQUAL_OP() {
  return getToken(SV3_1aPpParser::EQUAL_OP, 0);
}

tree::TerminalNode* SV3_1aPpParser::Text_blobContext::DOUBLE_QUOTE() {
  return getToken(SV3_1aPpParser::DOUBLE_QUOTE, 0);
}

tree::TerminalNode* SV3_1aPpParser::Text_blobContext::CURLY_OPEN() {
  return getToken(SV3_1aPpParser::CURLY_OPEN, 0);
}

tree::TerminalNode* SV3_1aPpParser::Text_blobContext::CURLY_CLOSE() {
  return getToken(SV3_1aPpParser::CURLY_CLOSE, 0);
}

tree::TerminalNode* SV3_1aPpParser::Text_blobContext::SQUARE_OPEN() {
  return getToken(SV3_1aPpParser::SQUARE_OPEN, 0);
}

tree::TerminalNode* SV3_1aPpParser::Text_blobContext::SQUARE_CLOSE() {
  return getToken(SV3_1aPpParser::SQUARE_CLOSE, 0);
}

tree::TerminalNode* SV3_1aPpParser::Text_blobContext::TICK_TICK() {
  return getToken(SV3_1aPpParser::TICK_TICK, 0);
}

tree::TerminalNode* SV3_1aPpParser::Text_blobContext::TICK_VARIABLE() {
  return getToken(SV3_1aPpParser::TICK_VARIABLE, 0);
}

tree::TerminalNode* SV3_1aPpParser::Text_blobContext::TIMESCALE() {
  return getToken(SV3_1aPpParser::TIMESCALE, 0);
}

SV3_1aPpParser::Pound_delayContext* SV3_1aPpParser::Text_blobContext::pound_delay() {
  return getRuleContext<SV3_1aPpParser::Pound_delayContext>(0);
}

SV3_1aPpParser::Pound_pound_delayContext* SV3_1aPpParser::Text_blobContext::pound_pound_delay() {
  return getRuleContext<SV3_1aPpParser::Pound_pound_delayContext>(0);
}

tree::TerminalNode* SV3_1aPpParser::Text_blobContext::TICK_QUOTE() {
  return getToken(SV3_1aPpParser::TICK_QUOTE, 0);
}

tree::TerminalNode* SV3_1aPpParser::Text_blobContext::TICK_BACKSLASH_TICK_QUOTE() {
  return getToken(SV3_1aPpParser::TICK_BACKSLASH_TICK_QUOTE, 0);
}

tree::TerminalNode* SV3_1aPpParser::Text_blobContext::TEXT_CR() {
  return getToken(SV3_1aPpParser::TEXT_CR, 0);
}

tree::TerminalNode* SV3_1aPpParser::Text_blobContext::Special() {
  return getToken(SV3_1aPpParser::Special, 0);
}

tree::TerminalNode* SV3_1aPpParser::Text_blobContext::ANY() {
  return getToken(SV3_1aPpParser::ANY, 0);
}


size_t SV3_1aPpParser::Text_blobContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleText_blob;
}

void SV3_1aPpParser::Text_blobContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterText_blob(this);
}

void SV3_1aPpParser::Text_blobContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitText_blob(this);
}

SV3_1aPpParser::Text_blobContext* SV3_1aPpParser::text_blob() {
  Text_blobContext *_localctx = _tracker.createInstance<Text_blobContext>(_ctx, getState());
  enterRule(_localctx, 192, SV3_1aPpParser::RuleText_blob);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    setState(1158);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case SV3_1aPpParser::Simple_identifier: {
        enterOuterAlt(_localctx, 1);
        setState(1132);
        match(SV3_1aPpParser::Simple_identifier);
        break;
      }

      case SV3_1aPpParser::Number: {
        enterOuterAlt(_localctx, 2);
        setState(1133);
        number();
        break;
      }

      case SV3_1aPpParser::CR: {
        enterOuterAlt(_localctx, 3);
        setState(1134);
        match(SV3_1aPpParser::CR);
        break;
      }

      case SV3_1aPpParser::Spaces: {
        enterOuterAlt(_localctx, 4);
        setState(1135);
        match(SV3_1aPpParser::Spaces);
        break;
      }

      case SV3_1aPpParser::Fixed_point_number: {
        enterOuterAlt(_localctx, 5);
        setState(1136);
        match(SV3_1aPpParser::Fixed_point_number);
        break;
      }

      case SV3_1aPpParser::ESCAPED_CR: {
        enterOuterAlt(_localctx, 6);
        setState(1137);
        match(SV3_1aPpParser::ESCAPED_CR);
        break;
      }

      case SV3_1aPpParser::String: {
        enterOuterAlt(_localctx, 7);
        setState(1138);
        match(SV3_1aPpParser::String);
        break;
      }

      case SV3_1aPpParser::PARENS_OPEN: {
        enterOuterAlt(_localctx, 8);
        setState(1139);
        match(SV3_1aPpParser::PARENS_OPEN);
        break;
      }

      case SV3_1aPpParser::PARENS_CLOSE: {
        enterOuterAlt(_localctx, 9);
        setState(1140);
        match(SV3_1aPpParser::PARENS_CLOSE);
        break;
      }

      case SV3_1aPpParser::COMMA: {
        enterOuterAlt(_localctx, 10);
        setState(1141);
        match(SV3_1aPpParser::COMMA);
        break;
      }

      case SV3_1aPpParser::EQUAL_OP: {
        enterOuterAlt(_localctx, 11);
        setState(1142);
        match(SV3_1aPpParser::EQUAL_OP);
        break;
      }

      case SV3_1aPpParser::DOUBLE_QUOTE: {
        enterOuterAlt(_localctx, 12);
        setState(1143);
        match(SV3_1aPpParser::DOUBLE_QUOTE);
        break;
      }

      case SV3_1aPpParser::CURLY_OPEN: {
        enterOuterAlt(_localctx, 13);
        setState(1144);
        match(SV3_1aPpParser::CURLY_OPEN);
        break;
      }

      case SV3_1aPpParser::CURLY_CLOSE: {
        enterOuterAlt(_localctx, 14);
        setState(1145);
        match(SV3_1aPpParser::CURLY_CLOSE);
        break;
      }

      case SV3_1aPpParser::SQUARE_OPEN: {
        enterOuterAlt(_localctx, 15);
        setState(1146);
        match(SV3_1aPpParser::SQUARE_OPEN);
        break;
      }

      case SV3_1aPpParser::SQUARE_CLOSE: {
        enterOuterAlt(_localctx, 16);
        setState(1147);
        match(SV3_1aPpParser::SQUARE_CLOSE);
        break;
      }

      case SV3_1aPpParser::TICK_TICK: {
        enterOuterAlt(_localctx, 17);
        setState(1148);
        match(SV3_1aPpParser::TICK_TICK);
        break;
      }

      case SV3_1aPpParser::TICK_VARIABLE: {
        enterOuterAlt(_localctx, 18);
        setState(1149);
        match(SV3_1aPpParser::TICK_VARIABLE);
        break;
      }

      case SV3_1aPpParser::TIMESCALE: {
        enterOuterAlt(_localctx, 19);
        setState(1150);
        match(SV3_1aPpParser::TIMESCALE);
        break;
      }

      case SV3_1aPpParser::Pound_delay: {
        enterOuterAlt(_localctx, 20);
        setState(1151);
        pound_delay();
        break;
      }

      case SV3_1aPpParser::Pound_Pound_delay: {
        enterOuterAlt(_localctx, 21);
        setState(1152);
        pound_pound_delay();
        break;
      }

      case SV3_1aPpParser::TICK_QUOTE: {
        enterOuterAlt(_localctx, 22);
        setState(1153);
        match(SV3_1aPpParser::TICK_QUOTE);
        break;
      }

      case SV3_1aPpParser::TICK_BACKSLASH_TICK_QUOTE: {
        enterOuterAlt(_localctx, 23);
        setState(1154);
        match(SV3_1aPpParser::TICK_BACKSLASH_TICK_QUOTE);
        break;
      }

      case SV3_1aPpParser::TEXT_CR: {
        enterOuterAlt(_localctx, 24);
        setState(1155);
        match(SV3_1aPpParser::TEXT_CR);
        break;
      }

      case SV3_1aPpParser::Special: {
        enterOuterAlt(_localctx, 25);
        setState(1156);
        match(SV3_1aPpParser::Special);
        break;
      }

      case SV3_1aPpParser::ANY: {
        enterOuterAlt(_localctx, 26);
        setState(1157);
        match(SV3_1aPpParser::ANY);
        break;
      }

    default:
      throw NoViableAltException(this);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- StringContext ------------------------------------------------------------------

SV3_1aPpParser::StringContext::StringContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::StringContext::String() {
  return getToken(SV3_1aPpParser::String, 0);
}


size_t SV3_1aPpParser::StringContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleString;
}

void SV3_1aPpParser::StringContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterString(this);
}

void SV3_1aPpParser::StringContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitString(this);
}

SV3_1aPpParser::StringContext* SV3_1aPpParser::string() {
  StringContext *_localctx = _tracker.createInstance<StringContext>(_ctx, getState());
  enterRule(_localctx, 194, SV3_1aPpParser::RuleString);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(1160);
    match(SV3_1aPpParser::String);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Escaped_identifierContext ------------------------------------------------------------------

SV3_1aPpParser::Escaped_identifierContext::Escaped_identifierContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Escaped_identifierContext::Escaped_identifier() {
  return getToken(SV3_1aPpParser::Escaped_identifier, 0);
}


size_t SV3_1aPpParser::Escaped_identifierContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleEscaped_identifier;
}

void SV3_1aPpParser::Escaped_identifierContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterEscaped_identifier(this);
}

void SV3_1aPpParser::Escaped_identifierContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitEscaped_identifier(this);
}

SV3_1aPpParser::Escaped_identifierContext* SV3_1aPpParser::escaped_identifier() {
  Escaped_identifierContext *_localctx = _tracker.createInstance<Escaped_identifierContext>(_ctx, getState());
  enterRule(_localctx, 196, SV3_1aPpParser::RuleEscaped_identifier);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(1162);
    match(SV3_1aPpParser::Escaped_identifier);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Default_valueContext ------------------------------------------------------------------

SV3_1aPpParser::Default_valueContext::Default_valueContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::Default_valueContext::Simple_identifier() {
  return getToken(SV3_1aPpParser::Simple_identifier, 0);
}

SV3_1aPpParser::NumberContext* SV3_1aPpParser::Default_valueContext::number() {
  return getRuleContext<SV3_1aPpParser::NumberContext>(0);
}

tree::TerminalNode* SV3_1aPpParser::Default_valueContext::Spaces() {
  return getToken(SV3_1aPpParser::Spaces, 0);
}

tree::TerminalNode* SV3_1aPpParser::Default_valueContext::Fixed_point_number() {
  return getToken(SV3_1aPpParser::Fixed_point_number, 0);
}

tree::TerminalNode* SV3_1aPpParser::Default_valueContext::String() {
  return getToken(SV3_1aPpParser::String, 0);
}

tree::TerminalNode* SV3_1aPpParser::Default_valueContext::CURLY_OPEN() {
  return getToken(SV3_1aPpParser::CURLY_OPEN, 0);
}

tree::TerminalNode* SV3_1aPpParser::Default_valueContext::CURLY_CLOSE() {
  return getToken(SV3_1aPpParser::CURLY_CLOSE, 0);
}

tree::TerminalNode* SV3_1aPpParser::Default_valueContext::SQUARE_OPEN() {
  return getToken(SV3_1aPpParser::SQUARE_OPEN, 0);
}

tree::TerminalNode* SV3_1aPpParser::Default_valueContext::SQUARE_CLOSE() {
  return getToken(SV3_1aPpParser::SQUARE_CLOSE, 0);
}

SV3_1aPpParser::Paired_parensContext* SV3_1aPpParser::Default_valueContext::paired_parens() {
  return getRuleContext<SV3_1aPpParser::Paired_parensContext>(0);
}

SV3_1aPpParser::Escaped_identifierContext* SV3_1aPpParser::Default_valueContext::escaped_identifier() {
  return getRuleContext<SV3_1aPpParser::Escaped_identifierContext>(0);
}

SV3_1aPpParser::Macro_instanceContext* SV3_1aPpParser::Default_valueContext::macro_instance() {
  return getRuleContext<SV3_1aPpParser::Macro_instanceContext>(0);
}

tree::TerminalNode* SV3_1aPpParser::Default_valueContext::Special() {
  return getToken(SV3_1aPpParser::Special, 0);
}

tree::TerminalNode* SV3_1aPpParser::Default_valueContext::ANY() {
  return getToken(SV3_1aPpParser::ANY, 0);
}


size_t SV3_1aPpParser::Default_valueContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleDefault_value;
}

void SV3_1aPpParser::Default_valueContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterDefault_value(this);
}

void SV3_1aPpParser::Default_valueContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitDefault_value(this);
}

SV3_1aPpParser::Default_valueContext* SV3_1aPpParser::default_value() {
  Default_valueContext *_localctx = _tracker.createInstance<Default_valueContext>(_ctx, getState());
  enterRule(_localctx, 198, SV3_1aPpParser::RuleDefault_value);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    setState(1178);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 79, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(1164);
      match(SV3_1aPpParser::Simple_identifier);
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(1165);
      number();
      break;
    }

    case 3: {
      enterOuterAlt(_localctx, 3);
      setState(1166);
      match(SV3_1aPpParser::Spaces);
      break;
    }

    case 4: {
      enterOuterAlt(_localctx, 4);
      setState(1167);
      match(SV3_1aPpParser::Fixed_point_number);
      break;
    }

    case 5: {
      enterOuterAlt(_localctx, 5);
      setState(1168);
      match(SV3_1aPpParser::String);
      break;
    }

    case 6: {
      enterOuterAlt(_localctx, 6);
      setState(1169);
      match(SV3_1aPpParser::CURLY_OPEN);
      break;
    }

    case 7: {
      enterOuterAlt(_localctx, 7);
      setState(1170);
      match(SV3_1aPpParser::CURLY_CLOSE);
      break;
    }

    case 8: {
      enterOuterAlt(_localctx, 8);
      setState(1171);
      match(SV3_1aPpParser::SQUARE_OPEN);
      break;
    }

    case 9: {
      enterOuterAlt(_localctx, 9);
      setState(1172);
      match(SV3_1aPpParser::SQUARE_CLOSE);
      break;
    }

    case 10: {
      enterOuterAlt(_localctx, 10);
      setState(1173);
      paired_parens();
      break;
    }

    case 11: {
      enterOuterAlt(_localctx, 11);
      setState(1174);
      escaped_identifier();
      break;
    }

    case 12: {
      enterOuterAlt(_localctx, 12);
      setState(1175);
      macro_instance();
      break;
    }

    case 13: {
      enterOuterAlt(_localctx, 13);
      setState(1176);
      match(SV3_1aPpParser::Special);
      break;
    }

    case 14: {
      enterOuterAlt(_localctx, 14);
      setState(1177);
      match(SV3_1aPpParser::ANY);
      break;
    }

    default:
      break;
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- String_blobContext ------------------------------------------------------------------

SV3_1aPpParser::String_blobContext::String_blobContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aPpParser::String_blobContext::Simple_identifier() {
  return getToken(SV3_1aPpParser::Simple_identifier, 0);
}

SV3_1aPpParser::NumberContext* SV3_1aPpParser::String_blobContext::number() {
  return getRuleContext<SV3_1aPpParser::NumberContext>(0);
}

tree::TerminalNode* SV3_1aPpParser::String_blobContext::Spaces() {
  return getToken(SV3_1aPpParser::Spaces, 0);
}

tree::TerminalNode* SV3_1aPpParser::String_blobContext::Fixed_point_number() {
  return getToken(SV3_1aPpParser::Fixed_point_number, 0);
}

tree::TerminalNode* SV3_1aPpParser::String_blobContext::ESCAPED_CR() {
  return getToken(SV3_1aPpParser::ESCAPED_CR, 0);
}

tree::TerminalNode* SV3_1aPpParser::String_blobContext::PARENS_OPEN() {
  return getToken(SV3_1aPpParser::PARENS_OPEN, 0);
}

tree::TerminalNode* SV3_1aPpParser::String_blobContext::PARENS_CLOSE() {
  return getToken(SV3_1aPpParser::PARENS_CLOSE, 0);
}

tree::TerminalNode* SV3_1aPpParser::String_blobContext::COMMA() {
  return getToken(SV3_1aPpParser::COMMA, 0);
}

tree::TerminalNode* SV3_1aPpParser::String_blobContext::EQUAL_OP() {
  return getToken(SV3_1aPpParser::EQUAL_OP, 0);
}

tree::TerminalNode* SV3_1aPpParser::String_blobContext::DOUBLE_QUOTE() {
  return getToken(SV3_1aPpParser::DOUBLE_QUOTE, 0);
}

tree::TerminalNode* SV3_1aPpParser::String_blobContext::CURLY_OPEN() {
  return getToken(SV3_1aPpParser::CURLY_OPEN, 0);
}

tree::TerminalNode* SV3_1aPpParser::String_blobContext::CURLY_CLOSE() {
  return getToken(SV3_1aPpParser::CURLY_CLOSE, 0);
}

tree::TerminalNode* SV3_1aPpParser::String_blobContext::SQUARE_OPEN() {
  return getToken(SV3_1aPpParser::SQUARE_OPEN, 0);
}

tree::TerminalNode* SV3_1aPpParser::String_blobContext::SQUARE_CLOSE() {
  return getToken(SV3_1aPpParser::SQUARE_CLOSE, 0);
}

SV3_1aPpParser::Escaped_identifierContext* SV3_1aPpParser::String_blobContext::escaped_identifier() {
  return getRuleContext<SV3_1aPpParser::Escaped_identifierContext>(0);
}

tree::TerminalNode* SV3_1aPpParser::String_blobContext::TIMESCALE() {
  return getToken(SV3_1aPpParser::TIMESCALE, 0);
}

SV3_1aPpParser::Pound_delayContext* SV3_1aPpParser::String_blobContext::pound_delay() {
  return getRuleContext<SV3_1aPpParser::Pound_delayContext>(0);
}

SV3_1aPpParser::Pound_pound_delayContext* SV3_1aPpParser::String_blobContext::pound_pound_delay() {
  return getRuleContext<SV3_1aPpParser::Pound_pound_delayContext>(0);
}

tree::TerminalNode* SV3_1aPpParser::String_blobContext::TEXT_CR() {
  return getToken(SV3_1aPpParser::TEXT_CR, 0);
}

tree::TerminalNode* SV3_1aPpParser::String_blobContext::Special() {
  return getToken(SV3_1aPpParser::Special, 0);
}

tree::TerminalNode* SV3_1aPpParser::String_blobContext::ANY() {
  return getToken(SV3_1aPpParser::ANY, 0);
}


size_t SV3_1aPpParser::String_blobContext::getRuleIndex() const {
  return SV3_1aPpParser::RuleString_blob;
}

void SV3_1aPpParser::String_blobContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterString_blob(this);
}

void SV3_1aPpParser::String_blobContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aPpParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitString_blob(this);
}

SV3_1aPpParser::String_blobContext* SV3_1aPpParser::string_blob() {
  String_blobContext *_localctx = _tracker.createInstance<String_blobContext>(_ctx, getState());
  enterRule(_localctx, 200, SV3_1aPpParser::RuleString_blob);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    setState(1201);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case SV3_1aPpParser::Simple_identifier: {
        enterOuterAlt(_localctx, 1);
        setState(1180);
        match(SV3_1aPpParser::Simple_identifier);
        break;
      }

      case SV3_1aPpParser::Number: {
        enterOuterAlt(_localctx, 2);
        setState(1181);
        number();
        break;
      }

      case SV3_1aPpParser::Spaces: {
        enterOuterAlt(_localctx, 3);
        setState(1182);
        match(SV3_1aPpParser::Spaces);
        break;
      }

      case SV3_1aPpParser::Fixed_point_number: {
        enterOuterAlt(_localctx, 4);
        setState(1183);
        match(SV3_1aPpParser::Fixed_point_number);
        break;
      }

      case SV3_1aPpParser::ESCAPED_CR: {
        enterOuterAlt(_localctx, 5);
        setState(1184);
        match(SV3_1aPpParser::ESCAPED_CR);
        break;
      }

      case SV3_1aPpParser::PARENS_OPEN: {
        enterOuterAlt(_localctx, 6);
        setState(1185);
        match(SV3_1aPpParser::PARENS_OPEN);
        break;
      }

      case SV3_1aPpParser::PARENS_CLOSE: {
        enterOuterAlt(_localctx, 7);
        setState(1186);
        match(SV3_1aPpParser::PARENS_CLOSE);
        break;
      }

      case SV3_1aPpParser::COMMA: {
        enterOuterAlt(_localctx, 8);
        setState(1187);
        match(SV3_1aPpParser::COMMA);
        break;
      }

      case SV3_1aPpParser::EQUAL_OP: {
        enterOuterAlt(_localctx, 9);
        setState(1188);
        match(SV3_1aPpParser::EQUAL_OP);
        break;
      }

      case SV3_1aPpParser::DOUBLE_QUOTE: {
        enterOuterAlt(_localctx, 10);
        setState(1189);
        match(SV3_1aPpParser::DOUBLE_QUOTE);
        break;
      }

      case SV3_1aPpParser::CURLY_OPEN: {
        enterOuterAlt(_localctx, 11);
        setState(1190);
        match(SV3_1aPpParser::CURLY_OPEN);
        break;
      }

      case SV3_1aPpParser::CURLY_CLOSE: {
        enterOuterAlt(_localctx, 12);
        setState(1191);
        match(SV3_1aPpParser::CURLY_CLOSE);
        break;
      }

      case SV3_1aPpParser::SQUARE_OPEN: {
        enterOuterAlt(_localctx, 13);
        setState(1192);
        match(SV3_1aPpParser::SQUARE_OPEN);
        break;
      }

      case SV3_1aPpParser::SQUARE_CLOSE: {
        enterOuterAlt(_localctx, 14);
        setState(1193);
        match(SV3_1aPpParser::SQUARE_CLOSE);
        break;
      }

      case SV3_1aPpParser::Escaped_identifier: {
        enterOuterAlt(_localctx, 15);
        setState(1194);
        escaped_identifier();
        break;
      }

      case SV3_1aPpParser::TIMESCALE: {
        enterOuterAlt(_localctx, 16);
        setState(1195);
        match(SV3_1aPpParser::TIMESCALE);
        break;
      }

      case SV3_1aPpParser::Pound_delay: {
        enterOuterAlt(_localctx, 17);
        setState(1196);
        pound_delay();
        break;
      }

      case SV3_1aPpParser::Pound_Pound_delay: {
        enterOuterAlt(_localctx, 18);
        setState(1197);
        pound_pound_delay();
        break;
      }

      case SV3_1aPpParser::TEXT_CR: {
        enterOuterAlt(_localctx, 19);
        setState(1198);
        match(SV3_1aPpParser::TEXT_CR);
        break;
      }

      case SV3_1aPpParser::Special: {
        enterOuterAlt(_localctx, 20);
        setState(1199);
        match(SV3_1aPpParser::Special);
        break;
      }

      case SV3_1aPpParser::ANY: {
        enterOuterAlt(_localctx, 21);
        setState(1200);
        match(SV3_1aPpParser::ANY);
        break;
      }

    default:
      throw NoViableAltException(this);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

// Static vars and initialization.
std::vector<dfa::DFA> SV3_1aPpParser::_decisionToDFA;
atn::PredictionContextCache SV3_1aPpParser::_sharedContextCache;

// We own the ATN which in turn owns the ATN states.
atn::ATN SV3_1aPpParser::_atn;
std::vector<uint16_t> SV3_1aPpParser::_serializedATN;

std::vector<std::string> SV3_1aPpParser::_ruleNames = {
  "top_level_rule", "source_text", "null_rule", "description", "macro_instance", 
  "unterminated_string", "macro_actual_args", "comments", "number", "pound_delay", 
  "pound_pound_delay", "macro_definition", "include_directive", "line_directive", 
  "default_nettype_directive", "sv_file_directive", "sv_line_directive", 
  "timescale_directive", "undef_directive", "ifdef_directive", "ifdef_directive_in_macro_body", 
  "ifndef_directive", "ifndef_directive_in_macro_body", "elsif_directive", 
  "elsif_directive_in_macro_body", "elseif_directive", "elseif_directive_in_macro_body", 
  "else_directive", "endif_directive", "resetall_directive", "begin_keywords_directive", 
  "end_keywords_directive", "pragma_directive", "celldefine_directive", 
  "endcelldefine_directive", "protect_directive", "endprotect_directive", 
  "protected_directive", "endprotected_directive", "expand_vectornets_directive", 
  "noexpand_vectornets_directive", "autoexpand_vectornets_directive", "uselib_directive", 
  "disable_portfaults_directive", "enable_portfaults_directive", "nosuppress_faults_directive", 
  "suppress_faults_directive", "signed_directive", "unsigned_directive", 
  "remove_gatename_directive", "noremove_gatenames_directive", "remove_netname_directive", 
  "noremove_netnames_directive", "accelerate_directive", "noaccelerate_directive", 
  "default_trireg_strenght_directive", "default_decay_time_directive", "unconnected_drive_directive", 
  "nounconnected_drive_directive", "delay_mode_distributed_directive", "delay_mode_path_directive", 
  "delay_mode_unit_directive", "delay_mode_zero_directive", "undefineall_directive", 
  "module", "endmodule", "sv_interface", "endinterface", "program", "endprogram", 
  "primitive", "endprimitive", "sv_package", "endpackage", "checker", "endchecker", 
  "config", "endconfig", "define_directive", "multiline_no_args_macro_definition", 
  "multiline_args_macro_definition", "simple_no_args_macro_definition", 
  "simple_args_macro_definition", "identifier_in_macro_body", "simple_no_args_macro_definition_in_macro_body", 
  "simple_args_macro_definition_in_macro_body", "directive_in_macro", "macro_arguments", 
  "escaped_macro_definition_body", "escaped_macro_definition_body_alt1", 
  "escaped_macro_definition_body_alt2", "simple_macro_definition_body", 
  "simple_macro_definition_body_in_macro_body", "pragma_expression", "macro_arg", 
  "paired_parens", "text_blob", "string", "escaped_identifier", "default_value", 
  "string_blob"
};

std::vector<std::string> SV3_1aPpParser::_literalNames = {
  "", "", "", "", "'`define'", "'`celldefine'", "'`endcelldefine'", "'`default_nettype'", 
  "'`undef'", "'`ifdef'", "'`ifndef'", "'`else'", "'`elsif'", "'`elseif'", 
  "'`endif'", "'`include'", "'`pragma'", "'`begin_keywords'", "'`end_keywords'", 
  "'`resetall'", "'`timescale'", "'`unconnected_drive'", "'`nounconnected_drive'", 
  "'`line'", "'`default_decay_time'", "'`default_trireg_strength'", "'`delay_mode_distributed'", 
  "'`delay_mode_path'", "'`delay_mode_unit'", "'`delay_mode_zero'", "'`undefineall'", 
  "'`accelerate'", "'`noaccelerate'", "'`protect'", "'`uselib'", "'`disable_portfaults'", 
  "'`enable_portfaults'", "'`nosuppress_faults'", "'`suppress_faults'", 
  "'`signed'", "'`unsigned'", "'`endprotect'", "'`protected'", "'`endprotected'", 
  "'`expand_vectornets'", "'`noexpand_vectornets'", "'`autoexpand_vectornets'", 
  "'`remove_gatename'", "'`noremove_gatenames'", "'`remove_netname'", "'`noremove_netnames'", 
  "'`__FILE__'", "'`__LINE__'", "'module'", "'endmodule'", "'interface'", 
  "'endinterface'", "'program'", "'endprogram'", "'primivite'", "'endprimitive'", 
  "'package'", "'endpackage'", "'checker'", "'endchecker'", "'config'", 
  "'endconfig'", "", "", "", "", "", "", "", "", "", "", "", "", "", "'`\"'", 
  "'`\\`\"'", "'``'", "'('", "')'", "','", "'='", "'\"'", "", "'{'", "'}'", 
  "'['", "']'"
};

std::vector<std::string> SV3_1aPpParser::_symbolicNames = {
  "", "One_line_comment", "Block_comment", "TICK_VARIABLE", "TICK_DEFINE", 
  "TICK_CELLDEFINE", "TICK_ENDCELLDEFINE", "TICK_DEFAULT_NETTYPE", "TICK_UNDEF", 
  "TICK_IFDEF", "TICK_IFNDEF", "TICK_ELSE", "TICK_ELSIF", "TICK_ELSEIF", 
  "TICK_ENDIF", "TICK_INCLUDE", "TICK_PRAGMA", "TICK_BEGIN_KEYWORDS", "TICK_END_KEYWORDS", 
  "TICK_RESETALL", "TICK_TIMESCALE", "TICK_UNCONNECTED_DRIVE", "TICK_NOUNCONNECTED_DRIVE", 
  "TICK_LINE", "TICK_DEFAULT_DECAY_TIME", "TICK_DEFAULT_TRIREG_STRENGTH", 
  "TICK_DELAY_MODE_DISTRIBUTED", "TICK_DELAY_MODE_PATH", "TICK_DELAY_MODE_UNIT", 
  "TICK_DELAY_MODE_ZERO", "TICK_UNDEFINEALL", "TICK_ACCELERATE", "TICK_NOACCELERATE", 
  "TICK_PROTECT", "TICK_USELIB", "TICK_DISABLE_PORTFAULTS", "TICK_ENABLE_PORTFAULTS", 
  "TICK_NOSUPPRESS_FAULTS", "TICK_SUPPRESS_FAULTS", "TICK_SIGNED", "TICK_UNSIGNED", 
  "TICK_ENDPROTECT", "TICK_PROTECTED", "TICK_ENDPROTECTED", "TICK_EXPAND_VECTORNETS", 
  "TICK_NOEXPAND_VECTORNETS", "TICK_AUTOEXPAND_VECTORNETS", "TICK_REMOVE_GATENAME", 
  "TICK_NOREMOVE_GATENAMES", "TICK_REMOVE_NETNAME", "TICK_NOREMOVE_NETNAMES", 
  "TICK_FILE__", "TICK_LINE__", "MODULE", "ENDMODULE", "INTERFACE", "ENDINTERFACE", 
  "PROGRAM", "ENDPROGRAM", "PRIMITIVE", "ENDPRIMITIVE", "PACKAGE", "ENDPACKAGE", 
  "CHECKER", "ENDCHECKER", "CONFIG", "ENDCONFIG", "Macro_identifier", "Macro_Escaped_identifier", 
  "String", "Simple_identifier", "Spaces", "Pound_Pound_delay", "Pound_delay", 
  "TIMESCALE", "Number", "Fixed_point_number", "TEXT_CR", "ESCAPED_CR", 
  "CR", "TICK_QUOTE", "TICK_BACKSLASH_TICK_QUOTE", "TICK_TICK", "PARENS_OPEN", 
  "PARENS_CLOSE", "COMMA", "EQUAL_OP", "DOUBLE_QUOTE", "Escaped_identifier", 
  "CURLY_OPEN", "CURLY_CLOSE", "SQUARE_OPEN", "SQUARE_CLOSE", "Special", 
  "ANY"
};

dfa::Vocabulary SV3_1aPpParser::_vocabulary(_literalNames, _symbolicNames);

std::vector<std::string> SV3_1aPpParser::_tokenNames;

SV3_1aPpParser::Initializer::Initializer() {
	for (size_t i = 0; i < _symbolicNames.size(); ++i) {
		std::string name = _vocabulary.getLiteralName(i);
		if (name.empty()) {
			name = _vocabulary.getSymbolicName(i);
		}

		if (name.empty()) {
			_tokenNames.push_back("<INVALID>");
		} else {
      _tokenNames.push_back(name);
    }
	}

  _serializedATN = {
    0x3, 0x608b, 0xa72a, 0x8133, 0xb9ed, 0x417c, 0x3be7, 0x7786, 0x5964, 
    0x3, 0x60, 0x4b6, 0x4, 0x2, 0x9, 0x2, 0x4, 0x3, 0x9, 0x3, 0x4, 0x4, 
    0x9, 0x4, 0x4, 0x5, 0x9, 0x5, 0x4, 0x6, 0x9, 0x6, 0x4, 0x7, 0x9, 0x7, 
    0x4, 0x8, 0x9, 0x8, 0x4, 0x9, 0x9, 0x9, 0x4, 0xa, 0x9, 0xa, 0x4, 0xb, 
    0x9, 0xb, 0x4, 0xc, 0x9, 0xc, 0x4, 0xd, 0x9, 0xd, 0x4, 0xe, 0x9, 0xe, 
    0x4, 0xf, 0x9, 0xf, 0x4, 0x10, 0x9, 0x10, 0x4, 0x11, 0x9, 0x11, 0x4, 
    0x12, 0x9, 0x12, 0x4, 0x13, 0x9, 0x13, 0x4, 0x14, 0x9, 0x14, 0x4, 0x15, 
    0x9, 0x15, 0x4, 0x16, 0x9, 0x16, 0x4, 0x17, 0x9, 0x17, 0x4, 0x18, 0x9, 
    0x18, 0x4, 0x19, 0x9, 0x19, 0x4, 0x1a, 0x9, 0x1a, 0x4, 0x1b, 0x9, 0x1b, 
    0x4, 0x1c, 0x9, 0x1c, 0x4, 0x1d, 0x9, 0x1d, 0x4, 0x1e, 0x9, 0x1e, 0x4, 
    0x1f, 0x9, 0x1f, 0x4, 0x20, 0x9, 0x20, 0x4, 0x21, 0x9, 0x21, 0x4, 0x22, 
    0x9, 0x22, 0x4, 0x23, 0x9, 0x23, 0x4, 0x24, 0x9, 0x24, 0x4, 0x25, 0x9, 
    0x25, 0x4, 0x26, 0x9, 0x26, 0x4, 0x27, 0x9, 0x27, 0x4, 0x28, 0x9, 0x28, 
    0x4, 0x29, 0x9, 0x29, 0x4, 0x2a, 0x9, 0x2a, 0x4, 0x2b, 0x9, 0x2b, 0x4, 
    0x2c, 0x9, 0x2c, 0x4, 0x2d, 0x9, 0x2d, 0x4, 0x2e, 0x9, 0x2e, 0x4, 0x2f, 
    0x9, 0x2f, 0x4, 0x30, 0x9, 0x30, 0x4, 0x31, 0x9, 0x31, 0x4, 0x32, 0x9, 
    0x32, 0x4, 0x33, 0x9, 0x33, 0x4, 0x34, 0x9, 0x34, 0x4, 0x35, 0x9, 0x35, 
    0x4, 0x36, 0x9, 0x36, 0x4, 0x37, 0x9, 0x37, 0x4, 0x38, 0x9, 0x38, 0x4, 
    0x39, 0x9, 0x39, 0x4, 0x3a, 0x9, 0x3a, 0x4, 0x3b, 0x9, 0x3b, 0x4, 0x3c, 
    0x9, 0x3c, 0x4, 0x3d, 0x9, 0x3d, 0x4, 0x3e, 0x9, 0x3e, 0x4, 0x3f, 0x9, 
    0x3f, 0x4, 0x40, 0x9, 0x40, 0x4, 0x41, 0x9, 0x41, 0x4, 0x42, 0x9, 0x42, 
    0x4, 0x43, 0x9, 0x43, 0x4, 0x44, 0x9, 0x44, 0x4, 0x45, 0x9, 0x45, 0x4, 
    0x46, 0x9, 0x46, 0x4, 0x47, 0x9, 0x47, 0x4, 0x48, 0x9, 0x48, 0x4, 0x49, 
    0x9, 0x49, 0x4, 0x4a, 0x9, 0x4a, 0x4, 0x4b, 0x9, 0x4b, 0x4, 0x4c, 0x9, 
    0x4c, 0x4, 0x4d, 0x9, 0x4d, 0x4, 0x4e, 0x9, 0x4e, 0x4, 0x4f, 0x9, 0x4f, 
    0x4, 0x50, 0x9, 0x50, 0x4, 0x51, 0x9, 0x51, 0x4, 0x52, 0x9, 0x52, 0x4, 
    0x53, 0x9, 0x53, 0x4, 0x54, 0x9, 0x54, 0x4, 0x55, 0x9, 0x55, 0x4, 0x56, 
    0x9, 0x56, 0x4, 0x57, 0x9, 0x57, 0x4, 0x58, 0x9, 0x58, 0x4, 0x59, 0x9, 
    0x59, 0x4, 0x5a, 0x9, 0x5a, 0x4, 0x5b, 0x9, 0x5b, 0x4, 0x5c, 0x9, 0x5c, 
    0x4, 0x5d, 0x9, 0x5d, 0x4, 0x5e, 0x9, 0x5e, 0x4, 0x5f, 0x9, 0x5f, 0x4, 
    0x60, 0x9, 0x60, 0x4, 0x61, 0x9, 0x61, 0x4, 0x62, 0x9, 0x62, 0x4, 0x63, 
    0x9, 0x63, 0x4, 0x64, 0x9, 0x64, 0x4, 0x65, 0x9, 0x65, 0x4, 0x66, 0x9, 
    0x66, 0x3, 0x2, 0x3, 0x2, 0x3, 0x2, 0x3, 0x2, 0x3, 0x3, 0x7, 0x3, 0xd2, 
    0xa, 0x3, 0xc, 0x3, 0xe, 0x3, 0xd5, 0xb, 0x3, 0x3, 0x4, 0x3, 0x4, 0x3, 
    0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 
    0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 
    0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 
    0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 
    0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 
    0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 
    0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 
    0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 
    0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 
    0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 
    0x5, 0x3, 0x5, 0x5, 0x5, 0x121, 0xa, 0x5, 0x3, 0x6, 0x3, 0x6, 0x7, 0x6, 
    0x125, 0xa, 0x6, 0xc, 0x6, 0xe, 0x6, 0x128, 0xb, 0x6, 0x3, 0x6, 0x3, 
    0x6, 0x3, 0x6, 0x3, 0x6, 0x3, 0x6, 0x5, 0x6, 0x12f, 0xa, 0x6, 0x3, 0x7, 
    0x3, 0x7, 0x7, 0x7, 0x133, 0xa, 0x7, 0xc, 0x7, 0xe, 0x7, 0x136, 0xb, 
    0x7, 0x3, 0x7, 0x3, 0x7, 0x3, 0x8, 0x7, 0x8, 0x13b, 0xa, 0x8, 0xc, 0x8, 
    0xe, 0x8, 0x13e, 0xb, 0x8, 0x3, 0x8, 0x3, 0x8, 0x7, 0x8, 0x142, 0xa, 
    0x8, 0xc, 0x8, 0xe, 0x8, 0x145, 0xb, 0x8, 0x7, 0x8, 0x147, 0xa, 0x8, 
    0xc, 0x8, 0xe, 0x8, 0x14a, 0xb, 0x8, 0x3, 0x9, 0x3, 0x9, 0x3, 0xa, 0x3, 
    0xa, 0x3, 0xb, 0x3, 0xb, 0x3, 0xc, 0x3, 0xc, 0x3, 0xd, 0x3, 0xd, 0x3, 
    0xd, 0x3, 0xd, 0x3, 0xd, 0x5, 0xd, 0x159, 0xa, 0xd, 0x3, 0xe, 0x3, 0xe, 
    0x3, 0xe, 0x3, 0xe, 0x3, 0xe, 0x3, 0xe, 0x5, 0xe, 0x161, 0xa, 0xe, 0x3, 
    0xf, 0x3, 0xf, 0x3, 0xf, 0x3, 0xf, 0x3, 0xf, 0x3, 0xf, 0x3, 0xf, 0x3, 
    0x10, 0x3, 0x10, 0x3, 0x10, 0x3, 0x10, 0x3, 0x11, 0x3, 0x11, 0x3, 0x12, 
    0x3, 0x12, 0x3, 0x13, 0x3, 0x13, 0x3, 0x13, 0x3, 0x14, 0x3, 0x14, 0x3, 
    0x14, 0x3, 0x14, 0x3, 0x14, 0x5, 0x14, 0x17a, 0xa, 0x14, 0x3, 0x15, 
    0x3, 0x15, 0x3, 0x15, 0x3, 0x15, 0x3, 0x15, 0x5, 0x15, 0x181, 0xa, 0x15, 
    0x3, 0x16, 0x3, 0x16, 0x3, 0x16, 0x3, 0x16, 0x3, 0x16, 0x5, 0x16, 0x188, 
    0xa, 0x16, 0x3, 0x17, 0x3, 0x17, 0x3, 0x17, 0x3, 0x17, 0x3, 0x17, 0x5, 
    0x17, 0x18f, 0xa, 0x17, 0x3, 0x18, 0x3, 0x18, 0x3, 0x18, 0x3, 0x18, 
    0x3, 0x18, 0x5, 0x18, 0x196, 0xa, 0x18, 0x3, 0x19, 0x3, 0x19, 0x3, 0x19, 
    0x3, 0x19, 0x3, 0x19, 0x5, 0x19, 0x19d, 0xa, 0x19, 0x3, 0x1a, 0x3, 0x1a, 
    0x3, 0x1a, 0x3, 0x1a, 0x3, 0x1a, 0x5, 0x1a, 0x1a4, 0xa, 0x1a, 0x3, 0x1b, 
    0x3, 0x1b, 0x3, 0x1b, 0x3, 0x1b, 0x3, 0x1b, 0x5, 0x1b, 0x1ab, 0xa, 0x1b, 
    0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x5, 0x1c, 0x1b2, 
    0xa, 0x1c, 0x3, 0x1d, 0x3, 0x1d, 0x3, 0x1e, 0x3, 0x1e, 0x7, 0x1e, 0x1b8, 
    0xa, 0x1e, 0xc, 0x1e, 0xe, 0x1e, 0x1bb, 0xb, 0x1e, 0x3, 0x1e, 0x3, 0x1e, 
    0x5, 0x1e, 0x1bf, 0xa, 0x1e, 0x3, 0x1f, 0x3, 0x1f, 0x3, 0x20, 0x3, 0x20, 
    0x3, 0x20, 0x3, 0x20, 0x3, 0x21, 0x3, 0x21, 0x3, 0x22, 0x3, 0x22, 0x3, 
    0x22, 0x3, 0x22, 0x3, 0x22, 0x3, 0x22, 0x7, 0x22, 0x1cf, 0xa, 0x22, 
    0xc, 0x22, 0xe, 0x22, 0x1d2, 0xb, 0x22, 0x7, 0x22, 0x1d4, 0xa, 0x22, 
    0xc, 0x22, 0xe, 0x22, 0x1d7, 0xb, 0x22, 0x3, 0x23, 0x3, 0x23, 0x7, 0x23, 
    0x1db, 0xa, 0x23, 0xc, 0x23, 0xe, 0x23, 0x1de, 0xb, 0x23, 0x3, 0x23, 
    0x3, 0x23, 0x3, 0x24, 0x3, 0x24, 0x7, 0x24, 0x1e4, 0xa, 0x24, 0xc, 0x24, 
    0xe, 0x24, 0x1e7, 0xb, 0x24, 0x3, 0x24, 0x3, 0x24, 0x3, 0x25, 0x3, 0x25, 
    0x7, 0x25, 0x1ed, 0xa, 0x25, 0xc, 0x25, 0xe, 0x25, 0x1f0, 0xb, 0x25, 
    0x3, 0x25, 0x3, 0x25, 0x3, 0x26, 0x3, 0x26, 0x7, 0x26, 0x1f6, 0xa, 0x26, 
    0xc, 0x26, 0xe, 0x26, 0x1f9, 0xb, 0x26, 0x3, 0x26, 0x3, 0x26, 0x3, 0x27, 
    0x3, 0x27, 0x3, 0x28, 0x3, 0x28, 0x3, 0x29, 0x3, 0x29, 0x3, 0x2a, 0x3, 
    0x2a, 0x3, 0x2b, 0x3, 0x2b, 0x3, 0x2c, 0x3, 0x2c, 0x6, 0x2c, 0x209, 
    0xa, 0x2c, 0xd, 0x2c, 0xe, 0x2c, 0x20a, 0x3, 0x2d, 0x3, 0x2d, 0x3, 0x2e, 
    0x3, 0x2e, 0x3, 0x2f, 0x3, 0x2f, 0x3, 0x30, 0x3, 0x30, 0x3, 0x31, 0x3, 
    0x31, 0x3, 0x32, 0x3, 0x32, 0x3, 0x33, 0x3, 0x33, 0x3, 0x34, 0x3, 0x34, 
    0x3, 0x35, 0x3, 0x35, 0x3, 0x36, 0x3, 0x36, 0x3, 0x37, 0x3, 0x37, 0x3, 
    0x38, 0x3, 0x38, 0x3, 0x39, 0x3, 0x39, 0x3, 0x39, 0x3, 0x39, 0x3, 0x3a, 
    0x3, 0x3a, 0x3, 0x3a, 0x3, 0x3a, 0x3, 0x3a, 0x5, 0x3a, 0x22e, 0xa, 0x3a, 
    0x3, 0x3b, 0x3, 0x3b, 0x3, 0x3b, 0x3, 0x3b, 0x3, 0x3c, 0x3, 0x3c, 0x7, 
    0x3c, 0x236, 0xa, 0x3c, 0xc, 0x3c, 0xe, 0x3c, 0x239, 0xb, 0x3c, 0x3, 
    0x3c, 0x3, 0x3c, 0x3, 0x3d, 0x3, 0x3d, 0x3, 0x3e, 0x3, 0x3e, 0x3, 0x3f, 
    0x3, 0x3f, 0x3, 0x40, 0x3, 0x40, 0x3, 0x41, 0x3, 0x41, 0x3, 0x42, 0x3, 
    0x42, 0x3, 0x43, 0x3, 0x43, 0x3, 0x44, 0x3, 0x44, 0x3, 0x45, 0x3, 0x45, 
    0x3, 0x46, 0x3, 0x46, 0x3, 0x47, 0x3, 0x47, 0x3, 0x48, 0x3, 0x48, 0x3, 
    0x49, 0x3, 0x49, 0x3, 0x4a, 0x3, 0x4a, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4c, 
    0x3, 0x4c, 0x3, 0x4d, 0x3, 0x4d, 0x3, 0x4e, 0x3, 0x4e, 0x3, 0x4f, 0x3, 
    0x4f, 0x3, 0x50, 0x3, 0x50, 0x3, 0x50, 0x3, 0x50, 0x7, 0x50, 0x267, 
    0xa, 0x50, 0xc, 0x50, 0xe, 0x50, 0x26a, 0xb, 0x50, 0x3, 0x50, 0x3, 0x50, 
    0x3, 0x51, 0x3, 0x51, 0x3, 0x51, 0x3, 0x51, 0x7, 0x51, 0x272, 0xa, 0x51, 
    0xc, 0x51, 0xe, 0x51, 0x275, 0xb, 0x51, 0x3, 0x51, 0x3, 0x51, 0x3, 0x52, 
    0x3, 0x52, 0x3, 0x52, 0x3, 0x52, 0x3, 0x52, 0x7, 0x52, 0x27e, 0xa, 0x52, 
    0xc, 0x52, 0xe, 0x52, 0x281, 0xb, 0x52, 0x3, 0x52, 0x3, 0x52, 0x3, 0x53, 
    0x3, 0x53, 0x3, 0x53, 0x3, 0x53, 0x3, 0x53, 0x3, 0x53, 0x3, 0x53, 0x3, 
    0x53, 0x3, 0x53, 0x3, 0x53, 0x3, 0x53, 0x7, 0x53, 0x290, 0xa, 0x53, 
    0xc, 0x53, 0xe, 0x53, 0x293, 0xb, 0x53, 0x3, 0x53, 0x5, 0x53, 0x296, 
    0xa, 0x53, 0x3, 0x54, 0x3, 0x54, 0x3, 0x54, 0x3, 0x54, 0x3, 0x54, 0x3, 
    0x54, 0x3, 0x54, 0x3, 0x54, 0x3, 0x54, 0x3, 0x54, 0x3, 0x54, 0x3, 0x54, 
    0x3, 0x54, 0x7, 0x54, 0x2a5, 0xa, 0x54, 0xc, 0x54, 0xe, 0x54, 0x2a8, 
    0xb, 0x54, 0x3, 0x54, 0x3, 0x54, 0x5, 0x54, 0x2ac, 0xa, 0x54, 0x3, 0x55, 
    0x3, 0x55, 0x5, 0x55, 0x2b0, 0xa, 0x55, 0x7, 0x55, 0x2b2, 0xa, 0x55, 
    0xc, 0x55, 0xe, 0x55, 0x2b5, 0xb, 0x55, 0x3, 0x56, 0x3, 0x56, 0x3, 0x56, 
    0x3, 0x56, 0x5, 0x56, 0x2bb, 0xa, 0x56, 0x3, 0x56, 0x3, 0x56, 0x3, 0x56, 
    0x3, 0x56, 0x3, 0x56, 0x3, 0x56, 0x5, 0x56, 0x2c3, 0xa, 0x56, 0x3, 0x56, 
    0x7, 0x56, 0x2c6, 0xa, 0x56, 0xc, 0x56, 0xe, 0x56, 0x2c9, 0xb, 0x56, 
    0x3, 0x56, 0x3, 0x56, 0x3, 0x56, 0x3, 0x56, 0x5, 0x56, 0x2cf, 0xa, 0x56, 
    0x3, 0x56, 0x3, 0x56, 0x5, 0x56, 0x2d3, 0xa, 0x56, 0x3, 0x57, 0x3, 0x57, 
    0x3, 0x57, 0x3, 0x57, 0x5, 0x57, 0x2d9, 0xa, 0x57, 0x3, 0x57, 0x3, 0x57, 
    0x3, 0x57, 0x3, 0x57, 0x3, 0x57, 0x3, 0x57, 0x3, 0x57, 0x3, 0x57, 0x5, 
    0x57, 0x2e3, 0xa, 0x57, 0x3, 0x57, 0x5, 0x57, 0x2e6, 0xa, 0x57, 0x3, 
    0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 
    0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 
    0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 
    0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 
    0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 
    0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 
    0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 
    0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 
    0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 
    0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x58, 0x5, 0x58, 0x327, 0xa, 0x58, 
    0x3, 0x59, 0x3, 0x59, 0x3, 0x59, 0x7, 0x59, 0x32c, 0xa, 0x59, 0xc, 0x59, 
    0xe, 0x59, 0x32f, 0xb, 0x59, 0x3, 0x59, 0x3, 0x59, 0x7, 0x59, 0x333, 
    0xa, 0x59, 0xc, 0x59, 0xe, 0x59, 0x336, 0xb, 0x59, 0x7, 0x59, 0x338, 
    0xa, 0x59, 0xc, 0x59, 0xe, 0x59, 0x33b, 0xb, 0x59, 0x3, 0x59, 0x3, 0x59, 
    0x7, 0x59, 0x33f, 0xa, 0x59, 0xc, 0x59, 0xe, 0x59, 0x342, 0xb, 0x59, 
    0x3, 0x59, 0x3, 0x59, 0x7, 0x59, 0x346, 0xa, 0x59, 0xc, 0x59, 0xe, 0x59, 
    0x349, 0xb, 0x59, 0x3, 0x59, 0x3, 0x59, 0x7, 0x59, 0x34d, 0xa, 0x59, 
    0xc, 0x59, 0xe, 0x59, 0x350, 0xb, 0x59, 0x7, 0x59, 0x352, 0xa, 0x59, 
    0xc, 0x59, 0xe, 0x59, 0x355, 0xb, 0x59, 0x7, 0x59, 0x357, 0xa, 0x59, 
    0xc, 0x59, 0xe, 0x59, 0x35a, 0xb, 0x59, 0x7, 0x59, 0x35c, 0xa, 0x59, 
    0xc, 0x59, 0xe, 0x59, 0x35f, 0xb, 0x59, 0x3, 0x59, 0x3, 0x59, 0x3, 0x5a, 
    0x3, 0x5a, 0x5, 0x5a, 0x365, 0xa, 0x5a, 0x3, 0x5b, 0x3, 0x5b, 0x3, 0x5b, 
    0x3, 0x5b, 0x3, 0x5b, 0x3, 0x5b, 0x3, 0x5b, 0x3, 0x5b, 0x3, 0x5b, 0x3, 
    0x5b, 0x3, 0x5b, 0x3, 0x5b, 0x3, 0x5b, 0x3, 0x5b, 0x3, 0x5b, 0x3, 0x5b, 
    0x3, 0x5b, 0x3, 0x5b, 0x3, 0x5b, 0x3, 0x5b, 0x3, 0x5b, 0x3, 0x5b, 0x3, 
    0x5b, 0x3, 0x5b, 0x3, 0x5b, 0x3, 0x5b, 0x3, 0x5b, 0x3, 0x5b, 0x3, 0x5b, 
    0x7, 0x5b, 0x384, 0xa, 0x5b, 0xc, 0x5b, 0xe, 0x5b, 0x387, 0xb, 0x5b, 
    0x3, 0x5b, 0x3, 0x5b, 0x7, 0x5b, 0x38b, 0xa, 0x5b, 0xc, 0x5b, 0xe, 0x5b, 
    0x38e, 0xb, 0x5b, 0x3, 0x5b, 0x3, 0x5b, 0x3, 0x5c, 0x3, 0x5c, 0x3, 0x5c, 
    0x3, 0x5c, 0x3, 0x5c, 0x3, 0x5c, 0x3, 0x5c, 0x3, 0x5c, 0x3, 0x5c, 0x3, 
    0x5c, 0x3, 0x5c, 0x3, 0x5c, 0x3, 0x5c, 0x3, 0x5c, 0x3, 0x5c, 0x3, 0x5c, 
    0x3, 0x5c, 0x3, 0x5c, 0x3, 0x5c, 0x3, 0x5c, 0x3, 0x5c, 0x3, 0x5c, 0x3, 
    0x5c, 0x3, 0x5c, 0x3, 0x5c, 0x3, 0x5c, 0x3, 0x5c, 0x3, 0x5c, 0x3, 0x5c, 
    0x7, 0x5c, 0x3af, 0xa, 0x5c, 0xc, 0x5c, 0xe, 0x5c, 0x3b2, 0xb, 0x5c, 
    0x3, 0x5c, 0x3, 0x5c, 0x7, 0x5c, 0x3b6, 0xa, 0x5c, 0xc, 0x5c, 0xe, 0x5c, 
    0x3b9, 0xb, 0x5c, 0x3, 0x5c, 0x5, 0x5c, 0x3bc, 0xa, 0x5c, 0x3, 0x5d, 
    0x3, 0x5d, 0x3, 0x5d, 0x3, 0x5d, 0x3, 0x5d, 0x3, 0x5d, 0x3, 0x5d, 0x3, 
    0x5d, 0x3, 0x5d, 0x3, 0x5d, 0x3, 0x5d, 0x3, 0x5d, 0x3, 0x5d, 0x3, 0x5d, 
    0x3, 0x5d, 0x3, 0x5d, 0x3, 0x5d, 0x3, 0x5d, 0x3, 0x5d, 0x3, 0x5d, 0x3, 
    0x5d, 0x3, 0x5d, 0x3, 0x5d, 0x3, 0x5d, 0x3, 0x5d, 0x3, 0x5d, 0x3, 0x5d, 
    0x3, 0x5d, 0x3, 0x5d, 0x7, 0x5d, 0x3db, 0xa, 0x5d, 0xc, 0x5d, 0xe, 0x5d, 
    0x3de, 0xb, 0x5d, 0x3, 0x5e, 0x3, 0x5e, 0x3, 0x5e, 0x3, 0x5e, 0x3, 0x5e, 
    0x3, 0x5e, 0x3, 0x5e, 0x3, 0x5e, 0x3, 0x5e, 0x3, 0x5e, 0x3, 0x5e, 0x3, 
    0x5e, 0x3, 0x5e, 0x3, 0x5e, 0x3, 0x5e, 0x3, 0x5e, 0x3, 0x5e, 0x3, 0x5e, 
    0x3, 0x5e, 0x3, 0x5e, 0x3, 0x5e, 0x3, 0x5e, 0x3, 0x5e, 0x3, 0x5e, 0x3, 
    0x5e, 0x3, 0x5e, 0x3, 0x5e, 0x7, 0x5e, 0x3fb, 0xa, 0x5e, 0xc, 0x5e, 
    0xe, 0x5e, 0x3fe, 0xb, 0x5e, 0x3, 0x5f, 0x3, 0x5f, 0x3, 0x5f, 0x3, 0x5f, 
    0x3, 0x5f, 0x3, 0x5f, 0x3, 0x5f, 0x3, 0x5f, 0x3, 0x5f, 0x3, 0x5f, 0x3, 
    0x5f, 0x3, 0x5f, 0x3, 0x5f, 0x3, 0x5f, 0x3, 0x5f, 0x3, 0x5f, 0x3, 0x5f, 
    0x3, 0x5f, 0x3, 0x5f, 0x5, 0x5f, 0x413, 0xa, 0x5f, 0x3, 0x60, 0x3, 0x60, 
    0x3, 0x60, 0x3, 0x60, 0x3, 0x60, 0x3, 0x60, 0x3, 0x60, 0x3, 0x60, 0x3, 
    0x60, 0x3, 0x60, 0x3, 0x60, 0x3, 0x60, 0x3, 0x60, 0x3, 0x60, 0x3, 0x60, 
    0x3, 0x60, 0x3, 0x60, 0x3, 0x60, 0x3, 0x60, 0x5, 0x60, 0x428, 0xa, 0x60, 
    0x3, 0x61, 0x3, 0x61, 0x3, 0x61, 0x3, 0x61, 0x3, 0x61, 0x3, 0x61, 0x3, 
    0x61, 0x3, 0x61, 0x3, 0x61, 0x3, 0x61, 0x3, 0x61, 0x3, 0x61, 0x3, 0x61, 
    0x3, 0x61, 0x3, 0x61, 0x3, 0x61, 0x3, 0x61, 0x7, 0x61, 0x43b, 0xa, 0x61, 
    0xc, 0x61, 0xe, 0x61, 0x43e, 0xb, 0x61, 0x3, 0x61, 0x3, 0x61, 0x3, 0x61, 
    0x3, 0x61, 0x3, 0x61, 0x3, 0x61, 0x3, 0x61, 0x3, 0x61, 0x3, 0x61, 0x3, 
    0x61, 0x3, 0x61, 0x3, 0x61, 0x3, 0x61, 0x3, 0x61, 0x3, 0x61, 0x3, 0x61, 
    0x3, 0x61, 0x7, 0x61, 0x451, 0xa, 0x61, 0xc, 0x61, 0xe, 0x61, 0x454, 
    0xb, 0x61, 0x3, 0x61, 0x3, 0x61, 0x3, 0x61, 0x3, 0x61, 0x3, 0x61, 0x3, 
    0x61, 0x3, 0x61, 0x3, 0x61, 0x3, 0x61, 0x3, 0x61, 0x3, 0x61, 0x3, 0x61, 
    0x3, 0x61, 0x3, 0x61, 0x3, 0x61, 0x3, 0x61, 0x3, 0x61, 0x7, 0x61, 0x467, 
    0xa, 0x61, 0xc, 0x61, 0xe, 0x61, 0x46a, 0xb, 0x61, 0x3, 0x61, 0x5, 0x61, 
    0x46d, 0xa, 0x61, 0x3, 0x62, 0x3, 0x62, 0x3, 0x62, 0x3, 0x62, 0x3, 0x62, 
    0x3, 0x62, 0x3, 0x62, 0x3, 0x62, 0x3, 0x62, 0x3, 0x62, 0x3, 0x62, 0x3, 
    0x62, 0x3, 0x62, 0x3, 0x62, 0x3, 0x62, 0x3, 0x62, 0x3, 0x62, 0x3, 0x62, 
    0x3, 0x62, 0x3, 0x62, 0x3, 0x62, 0x3, 0x62, 0x3, 0x62, 0x3, 0x62, 0x3, 
    0x62, 0x3, 0x62, 0x5, 0x62, 0x489, 0xa, 0x62, 0x3, 0x63, 0x3, 0x63, 
    0x3, 0x64, 0x3, 0x64, 0x3, 0x65, 0x3, 0x65, 0x3, 0x65, 0x3, 0x65, 0x3, 
    0x65, 0x3, 0x65, 0x3, 0x65, 0x3, 0x65, 0x3, 0x65, 0x3, 0x65, 0x3, 0x65, 
    0x3, 0x65, 0x3, 0x65, 0x3, 0x65, 0x5, 0x65, 0x49d, 0xa, 0x65, 0x3, 0x66, 
    0x3, 0x66, 0x3, 0x66, 0x3, 0x66, 0x3, 0x66, 0x3, 0x66, 0x3, 0x66, 0x3, 
    0x66, 0x3, 0x66, 0x3, 0x66, 0x3, 0x66, 0x3, 0x66, 0x3, 0x66, 0x3, 0x66, 
    0x3, 0x66, 0x3, 0x66, 0x3, 0x66, 0x3, 0x66, 0x3, 0x66, 0x3, 0x66, 0x3, 
    0x66, 0x5, 0x66, 0x4b4, 0xa, 0x66, 0x3, 0x66, 0x6, 0x385, 0x3b0, 0x3dc, 
    0x3fc, 0x2, 0x67, 0x2, 0x4, 0x6, 0x8, 0xa, 0xc, 0xe, 0x10, 0x12, 0x14, 
    0x16, 0x18, 0x1a, 0x1c, 0x1e, 0x20, 0x22, 0x24, 0x26, 0x28, 0x2a, 0x2c, 
    0x2e, 0x30, 0x32, 0x34, 0x36, 0x38, 0x3a, 0x3c, 0x3e, 0x40, 0x42, 0x44, 
    0x46, 0x48, 0x4a, 0x4c, 0x4e, 0x50, 0x52, 0x54, 0x56, 0x58, 0x5a, 0x5c, 
    0x5e, 0x60, 0x62, 0x64, 0x66, 0x68, 0x6a, 0x6c, 0x6e, 0x70, 0x72, 0x74, 
    0x76, 0x78, 0x7a, 0x7c, 0x7e, 0x80, 0x82, 0x84, 0x86, 0x88, 0x8a, 0x8c, 
    0x8e, 0x90, 0x92, 0x94, 0x96, 0x98, 0x9a, 0x9c, 0x9e, 0xa0, 0xa2, 0xa4, 
    0xa6, 0xa8, 0xaa, 0xac, 0xae, 0xb0, 0xb2, 0xb4, 0xb6, 0xb8, 0xba, 0xbc, 
    0xbe, 0xc0, 0xc2, 0xc4, 0xc6, 0xc8, 0xca, 0x2, 0x7, 0x3, 0x2, 0x45, 
    0x46, 0x3, 0x2, 0x3, 0x4, 0x4, 0x2, 0x48, 0x48, 0x5a, 0x5a, 0x4, 0x2, 
    0x3, 0x3, 0x51, 0x51, 0x3, 0x3, 0x51, 0x51, 0x2, 0x620, 0x2, 0xcc, 0x3, 
    0x2, 0x2, 0x2, 0x4, 0xd3, 0x3, 0x2, 0x2, 0x2, 0x6, 0xd6, 0x3, 0x2, 0x2, 
    0x2, 0x8, 0x120, 0x3, 0x2, 0x2, 0x2, 0xa, 0x12e, 0x3, 0x2, 0x2, 0x2, 
    0xc, 0x130, 0x3, 0x2, 0x2, 0x2, 0xe, 0x13c, 0x3, 0x2, 0x2, 0x2, 0x10, 
    0x14b, 0x3, 0x2, 0x2, 0x2, 0x12, 0x14d, 0x3, 0x2, 0x2, 0x2, 0x14, 0x14f, 
    0x3, 0x2, 0x2, 0x2, 0x16, 0x151, 0x3, 0x2, 0x2, 0x2, 0x18, 0x158, 0x3, 
    0x2, 0x2, 0x2, 0x1a, 0x15a, 0x3, 0x2, 0x2, 0x2, 0x1c, 0x162, 0x3, 0x2, 
    0x2, 0x2, 0x1e, 0x169, 0x3, 0x2, 0x2, 0x2, 0x20, 0x16d, 0x3, 0x2, 0x2, 
    0x2, 0x22, 0x16f, 0x3, 0x2, 0x2, 0x2, 0x24, 0x171, 0x3, 0x2, 0x2, 0x2, 
    0x26, 0x174, 0x3, 0x2, 0x2, 0x2, 0x28, 0x17b, 0x3, 0x2, 0x2, 0x2, 0x2a, 
    0x182, 0x3, 0x2, 0x2, 0x2, 0x2c, 0x189, 0x3, 0x2, 0x2, 0x2, 0x2e, 0x190, 
    0x3, 0x2, 0x2, 0x2, 0x30, 0x197, 0x3, 0x2, 0x2, 0x2, 0x32, 0x19e, 0x3, 
    0x2, 0x2, 0x2, 0x34, 0x1a5, 0x3, 0x2, 0x2, 0x2, 0x36, 0x1ac, 0x3, 0x2, 
    0x2, 0x2, 0x38, 0x1b3, 0x3, 0x2, 0x2, 0x2, 0x3a, 0x1be, 0x3, 0x2, 0x2, 
    0x2, 0x3c, 0x1c0, 0x3, 0x2, 0x2, 0x2, 0x3e, 0x1c2, 0x3, 0x2, 0x2, 0x2, 
    0x40, 0x1c6, 0x3, 0x2, 0x2, 0x2, 0x42, 0x1c8, 0x3, 0x2, 0x2, 0x2, 0x44, 
    0x1d8, 0x3, 0x2, 0x2, 0x2, 0x46, 0x1e1, 0x3, 0x2, 0x2, 0x2, 0x48, 0x1ea, 
    0x3, 0x2, 0x2, 0x2, 0x4a, 0x1f3, 0x3, 0x2, 0x2, 0x2, 0x4c, 0x1fc, 0x3, 
    0x2, 0x2, 0x2, 0x4e, 0x1fe, 0x3, 0x2, 0x2, 0x2, 0x50, 0x200, 0x3, 0x2, 
    0x2, 0x2, 0x52, 0x202, 0x3, 0x2, 0x2, 0x2, 0x54, 0x204, 0x3, 0x2, 0x2, 
    0x2, 0x56, 0x206, 0x3, 0x2, 0x2, 0x2, 0x58, 0x20c, 0x3, 0x2, 0x2, 0x2, 
    0x5a, 0x20e, 0x3, 0x2, 0x2, 0x2, 0x5c, 0x210, 0x3, 0x2, 0x2, 0x2, 0x5e, 
    0x212, 0x3, 0x2, 0x2, 0x2, 0x60, 0x214, 0x3, 0x2, 0x2, 0x2, 0x62, 0x216, 
    0x3, 0x2, 0x2, 0x2, 0x64, 0x218, 0x3, 0x2, 0x2, 0x2, 0x66, 0x21a, 0x3, 
    0x2, 0x2, 0x2, 0x68, 0x21c, 0x3, 0x2, 0x2, 0x2, 0x6a, 0x21e, 0x3, 0x2, 
    0x2, 0x2, 0x6c, 0x220, 0x3, 0x2, 0x2, 0x2, 0x6e, 0x222, 0x3, 0x2, 0x2, 
    0x2, 0x70, 0x224, 0x3, 0x2, 0x2, 0x2, 0x72, 0x228, 0x3, 0x2, 0x2, 0x2, 
    0x74, 0x22f, 0x3, 0x2, 0x2, 0x2, 0x76, 0x233, 0x3, 0x2, 0x2, 0x2, 0x78, 
    0x23c, 0x3, 0x2, 0x2, 0x2, 0x7a, 0x23e, 0x3, 0x2, 0x2, 0x2, 0x7c, 0x240, 
    0x3, 0x2, 0x2, 0x2, 0x7e, 0x242, 0x3, 0x2, 0x2, 0x2, 0x80, 0x244, 0x3, 
    0x2, 0x2, 0x2, 0x82, 0x246, 0x3, 0x2, 0x2, 0x2, 0x84, 0x248, 0x3, 0x2, 
    0x2, 0x2, 0x86, 0x24a, 0x3, 0x2, 0x2, 0x2, 0x88, 0x24c, 0x3, 0x2, 0x2, 
    0x2, 0x8a, 0x24e, 0x3, 0x2, 0x2, 0x2, 0x8c, 0x250, 0x3, 0x2, 0x2, 0x2, 
    0x8e, 0x252, 0x3, 0x2, 0x2, 0x2, 0x90, 0x254, 0x3, 0x2, 0x2, 0x2, 0x92, 
    0x256, 0x3, 0x2, 0x2, 0x2, 0x94, 0x258, 0x3, 0x2, 0x2, 0x2, 0x96, 0x25a, 
    0x3, 0x2, 0x2, 0x2, 0x98, 0x25c, 0x3, 0x2, 0x2, 0x2, 0x9a, 0x25e, 0x3, 
    0x2, 0x2, 0x2, 0x9c, 0x260, 0x3, 0x2, 0x2, 0x2, 0x9e, 0x262, 0x3, 0x2, 
    0x2, 0x2, 0xa0, 0x26d, 0x3, 0x2, 0x2, 0x2, 0xa2, 0x278, 0x3, 0x2, 0x2, 
    0x2, 0xa4, 0x295, 0x3, 0x2, 0x2, 0x2, 0xa6, 0x2ab, 0x3, 0x2, 0x2, 0x2, 
    0xa8, 0x2b3, 0x3, 0x2, 0x2, 0x2, 0xaa, 0x2d2, 0x3, 0x2, 0x2, 0x2, 0xac, 
    0x2e5, 0x3, 0x2, 0x2, 0x2, 0xae, 0x326, 0x3, 0x2, 0x2, 0x2, 0xb0, 0x328, 
    0x3, 0x2, 0x2, 0x2, 0xb2, 0x364, 0x3, 0x2, 0x2, 0x2, 0xb4, 0x385, 0x3, 
    0x2, 0x2, 0x2, 0xb6, 0x3b0, 0x3, 0x2, 0x2, 0x2, 0xb8, 0x3dc, 0x3, 0x2, 
    0x2, 0x2, 0xba, 0x3fc, 0x3, 0x2, 0x2, 0x2, 0xbc, 0x412, 0x3, 0x2, 0x2, 
    0x2, 0xbe, 0x427, 0x3, 0x2, 0x2, 0x2, 0xc0, 0x46c, 0x3, 0x2, 0x2, 0x2, 
    0xc2, 0x488, 0x3, 0x2, 0x2, 0x2, 0xc4, 0x48a, 0x3, 0x2, 0x2, 0x2, 0xc6, 
    0x48c, 0x3, 0x2, 0x2, 0x2, 0xc8, 0x49c, 0x3, 0x2, 0x2, 0x2, 0xca, 0x4b3, 
    0x3, 0x2, 0x2, 0x2, 0xcc, 0xcd, 0x5, 0x6, 0x4, 0x2, 0xcd, 0xce, 0x5, 
    0x4, 0x3, 0x2, 0xce, 0xcf, 0x7, 0x2, 0x2, 0x3, 0xcf, 0x3, 0x3, 0x2, 
    0x2, 0x2, 0xd0, 0xd2, 0x5, 0x8, 0x5, 0x2, 0xd1, 0xd0, 0x3, 0x2, 0x2, 
    0x2, 0xd2, 0xd5, 0x3, 0x2, 0x2, 0x2, 0xd3, 0xd1, 0x3, 0x2, 0x2, 0x2, 
    0xd3, 0xd4, 0x3, 0x2, 0x2, 0x2, 0xd4, 0x5, 0x3, 0x2, 0x2, 0x2, 0xd5, 
    0xd3, 0x3, 0x2, 0x2, 0x2, 0xd6, 0xd7, 0x3, 0x2, 0x2, 0x2, 0xd7, 0x7, 
    0x3, 0x2, 0x2, 0x2, 0xd8, 0x121, 0x5, 0xc, 0x7, 0x2, 0xd9, 0x121, 0x5, 
    0xc4, 0x63, 0x2, 0xda, 0x121, 0x5, 0x12, 0xa, 0x2, 0xdb, 0x121, 0x5, 
    0x18, 0xd, 0x2, 0xdc, 0x121, 0x5, 0x10, 0x9, 0x2, 0xdd, 0x121, 0x5, 
    0x44, 0x23, 0x2, 0xde, 0x121, 0x5, 0x46, 0x24, 0x2, 0xdf, 0x121, 0x5, 
    0x1e, 0x10, 0x2, 0xe0, 0x121, 0x5, 0x26, 0x14, 0x2, 0xe1, 0x121, 0x5, 
    0x28, 0x15, 0x2, 0xe2, 0x121, 0x5, 0x2c, 0x17, 0x2, 0xe3, 0x121, 0x5, 
    0x38, 0x1d, 0x2, 0xe4, 0x121, 0x5, 0x30, 0x19, 0x2, 0xe5, 0x121, 0x5, 
    0x34, 0x1b, 0x2, 0xe6, 0x121, 0x5, 0x3a, 0x1e, 0x2, 0xe7, 0x121, 0x5, 
    0x1a, 0xe, 0x2, 0xe8, 0x121, 0x5, 0x3c, 0x1f, 0x2, 0xe9, 0x121, 0x5, 
    0x3e, 0x20, 0x2, 0xea, 0x121, 0x5, 0x40, 0x21, 0x2, 0xeb, 0x121, 0x5, 
    0x24, 0x13, 0x2, 0xec, 0x121, 0x5, 0x74, 0x3b, 0x2, 0xed, 0x121, 0x5, 
    0x76, 0x3c, 0x2, 0xee, 0x121, 0x5, 0x1c, 0xf, 0x2, 0xef, 0x121, 0x5, 
    0x72, 0x3a, 0x2, 0xf0, 0x121, 0x5, 0x70, 0x39, 0x2, 0xf1, 0x121, 0x5, 
    0x78, 0x3d, 0x2, 0xf2, 0x121, 0x5, 0x7a, 0x3e, 0x2, 0xf3, 0x121, 0x5, 
    0x7c, 0x3f, 0x2, 0xf4, 0x121, 0x5, 0x7e, 0x40, 0x2, 0xf5, 0x121, 0x5, 
    0x48, 0x25, 0x2, 0xf6, 0x121, 0x5, 0x4a, 0x26, 0x2, 0xf7, 0x121, 0x5, 
    0x4c, 0x27, 0x2, 0xf8, 0x121, 0x5, 0x4e, 0x28, 0x2, 0xf9, 0x121, 0x5, 
    0x50, 0x29, 0x2, 0xfa, 0x121, 0x5, 0x52, 0x2a, 0x2, 0xfb, 0x121, 0x5, 
    0x54, 0x2b, 0x2, 0xfc, 0x121, 0x5, 0x64, 0x33, 0x2, 0xfd, 0x121, 0x5, 
    0x66, 0x34, 0x2, 0xfe, 0x121, 0x5, 0x68, 0x35, 0x2, 0xff, 0x121, 0x5, 
    0x6a, 0x36, 0x2, 0x100, 0x121, 0x5, 0x6c, 0x37, 0x2, 0x101, 0x121, 0x5, 
    0x6e, 0x38, 0x2, 0x102, 0x121, 0x5, 0x80, 0x41, 0x2, 0x103, 0x121, 0x5, 
    0x56, 0x2c, 0x2, 0x104, 0x121, 0x5, 0x58, 0x2d, 0x2, 0x105, 0x121, 0x5, 
    0x5a, 0x2e, 0x2, 0x106, 0x121, 0x5, 0x5c, 0x2f, 0x2, 0x107, 0x121, 0x5, 
    0x5e, 0x30, 0x2, 0x108, 0x121, 0x5, 0x60, 0x31, 0x2, 0x109, 0x121, 0x5, 
    0x62, 0x32, 0x2, 0x10a, 0x121, 0x5, 0x42, 0x22, 0x2, 0x10b, 0x121, 0x5, 
    0x20, 0x11, 0x2, 0x10c, 0x121, 0x5, 0x22, 0x12, 0x2, 0x10d, 0x121, 0x5, 
    0xa, 0x6, 0x2, 0x10e, 0x121, 0x5, 0x82, 0x42, 0x2, 0x10f, 0x121, 0x5, 
    0x84, 0x43, 0x2, 0x110, 0x121, 0x5, 0x86, 0x44, 0x2, 0x111, 0x121, 0x5, 
    0x88, 0x45, 0x2, 0x112, 0x121, 0x5, 0x8a, 0x46, 0x2, 0x113, 0x121, 0x5, 
    0x8c, 0x47, 0x2, 0x114, 0x121, 0x5, 0x8e, 0x48, 0x2, 0x115, 0x121, 0x5, 
    0x90, 0x49, 0x2, 0x116, 0x121, 0x5, 0x92, 0x4a, 0x2, 0x117, 0x121, 0x5, 
    0x94, 0x4b, 0x2, 0x118, 0x121, 0x5, 0x96, 0x4c, 0x2, 0x119, 0x121, 0x5, 
    0x98, 0x4d, 0x2, 0x11a, 0x121, 0x5, 0x9a, 0x4e, 0x2, 0x11b, 0x121, 0x5, 
    0x9c, 0x4f, 0x2, 0x11c, 0x121, 0x5, 0xc2, 0x62, 0x2, 0x11d, 0x121, 0x5, 
    0xc6, 0x64, 0x2, 0x11e, 0x121, 0x5, 0x14, 0xb, 0x2, 0x11f, 0x121, 0x5, 
    0x16, 0xc, 0x2, 0x120, 0xd8, 0x3, 0x2, 0x2, 0x2, 0x120, 0xd9, 0x3, 0x2, 
    0x2, 0x2, 0x120, 0xda, 0x3, 0x2, 0x2, 0x2, 0x120, 0xdb, 0x3, 0x2, 0x2, 
    0x2, 0x120, 0xdc, 0x3, 0x2, 0x2, 0x2, 0x120, 0xdd, 0x3, 0x2, 0x2, 0x2, 
    0x120, 0xde, 0x3, 0x2, 0x2, 0x2, 0x120, 0xdf, 0x3, 0x2, 0x2, 0x2, 0x120, 
    0xe0, 0x3, 0x2, 0x2, 0x2, 0x120, 0xe1, 0x3, 0x2, 0x2, 0x2, 0x120, 0xe2, 
    0x3, 0x2, 0x2, 0x2, 0x120, 0xe3, 0x3, 0x2, 0x2, 0x2, 0x120, 0xe4, 0x3, 
    0x2, 0x2, 0x2, 0x120, 0xe5, 0x3, 0x2, 0x2, 0x2, 0x120, 0xe6, 0x3, 0x2, 
    0x2, 0x2, 0x120, 0xe7, 0x3, 0x2, 0x2, 0x2, 0x120, 0xe8, 0x3, 0x2, 0x2, 
    0x2, 0x120, 0xe9, 0x3, 0x2, 0x2, 0x2, 0x120, 0xea, 0x3, 0x2, 0x2, 0x2, 
    0x120, 0xeb, 0x3, 0x2, 0x2, 0x2, 0x120, 0xec, 0x3, 0x2, 0x2, 0x2, 0x120, 
    0xed, 0x3, 0x2, 0x2, 0x2, 0x120, 0xee, 0x3, 0x2, 0x2, 0x2, 0x120, 0xef, 
    0x3, 0x2, 0x2, 0x2, 0x120, 0xf0, 0x3, 0x2, 0x2, 0x2, 0x120, 0xf1, 0x3, 
    0x2, 0x2, 0x2, 0x120, 0xf2, 0x3, 0x2, 0x2, 0x2, 0x120, 0xf3, 0x3, 0x2, 
    0x2, 0x2, 0x120, 0xf4, 0x3, 0x2, 0x2, 0x2, 0x120, 0xf5, 0x3, 0x2, 0x2, 
    0x2, 0x120, 0xf6, 0x3, 0x2, 0x2, 0x2, 0x120, 0xf7, 0x3, 0x2, 0x2, 0x2, 
    0x120, 0xf8, 0x3, 0x2, 0x2, 0x2, 0x120, 0xf9, 0x3, 0x2, 0x2, 0x2, 0x120, 
    0xfa, 0x3, 0x2, 0x2, 0x2, 0x120, 0xfb, 0x3, 0x2, 0x2, 0x2, 0x120, 0xfc, 
    0x3, 0x2, 0x2, 0x2, 0x120, 0xfd, 0x3, 0x2, 0x2, 0x2, 0x120, 0xfe, 0x3, 
    0x2, 0x2, 0x2, 0x120, 0xff, 0x3, 0x2, 0x2, 0x2, 0x120, 0x100, 0x3, 0x2, 
    0x2, 0x2, 0x120, 0x101, 0x3, 0x2, 0x2, 0x2, 0x120, 0x102, 0x3, 0x2, 
    0x2, 0x2, 0x120, 0x103, 0x3, 0x2, 0x2, 0x2, 0x120, 0x104, 0x3, 0x2, 
    0x2, 0x2, 0x120, 0x105, 0x3, 0x2, 0x2, 0x2, 0x120, 0x106, 0x3, 0x2, 
    0x2, 0x2, 0x120, 0x107, 0x3, 0x2, 0x2, 0x2, 0x120, 0x108, 0x3, 0x2, 
    0x2, 0x2, 0x120, 0x109, 0x3, 0x2, 0x2, 0x2, 0x120, 0x10a, 0x3, 0x2, 
    0x2, 0x2, 0x120, 0x10b, 0x3, 0x2, 0x2, 0x2, 0x120, 0x10c, 0x3, 0x2, 
    0x2, 0x2, 0x120, 0x10d, 0x3, 0x2, 0x2, 0x2, 0x120, 0x10e, 0x3, 0x2, 
    0x2, 0x2, 0x120, 0x10f, 0x3, 0x2, 0x2, 0x2, 0x120, 0x110, 0x3, 0x2, 
    0x2, 0x2, 0x120, 0x111, 0x3, 0x2, 0x2, 0x2, 0x120, 0x112, 0x3, 0x2, 
    0x2, 0x2, 0x120, 0x113, 0x3, 0x2, 0x2, 0x2, 0x120, 0x114, 0x3, 0x2, 
    0x2, 0x2, 0x120, 0x115, 0x3, 0x2, 0x2, 0x2, 0x120, 0x116, 0x3, 0x2, 
    0x2, 0x2, 0x120, 0x117, 0x3, 0x2, 0x2, 0x2, 0x120, 0x118, 0x3, 0x2, 
    0x2, 0x2, 0x120, 0x119, 0x3, 0x2, 0x2, 0x2, 0x120, 0x11a, 0x3, 0x2, 
    0x2, 0x2, 0x120, 0x11b, 0x3, 0x2, 0x2, 0x2, 0x120, 0x11c, 0x3, 0x2, 
    0x2, 0x2, 0x120, 0x11d, 0x3, 0x2, 0x2, 0x2, 0x120, 0x11e, 0x3, 0x2, 
    0x2, 0x2, 0x120, 0x11f, 0x3, 0x2, 0x2, 0x2, 0x121, 0x9, 0x3, 0x2, 0x2, 
    0x2, 0x122, 0x126, 0x9, 0x2, 0x2, 0x2, 0x123, 0x125, 0x7, 0x49, 0x2, 
    0x2, 0x124, 0x123, 0x3, 0x2, 0x2, 0x2, 0x125, 0x128, 0x3, 0x2, 0x2, 
    0x2, 0x126, 0x124, 0x3, 0x2, 0x2, 0x2, 0x126, 0x127, 0x3, 0x2, 0x2, 
    0x2, 0x127, 0x129, 0x3, 0x2, 0x2, 0x2, 0x128, 0x126, 0x3, 0x2, 0x2, 
    0x2, 0x129, 0x12a, 0x7, 0x55, 0x2, 0x2, 0x12a, 0x12b, 0x5, 0xe, 0x8, 
    0x2, 0x12b, 0x12c, 0x7, 0x56, 0x2, 0x2, 0x12c, 0x12f, 0x3, 0x2, 0x2, 
    0x2, 0x12d, 0x12f, 0x9, 0x2, 0x2, 0x2, 0x12e, 0x122, 0x3, 0x2, 0x2, 
    0x2, 0x12e, 0x12d, 0x3, 0x2, 0x2, 0x2, 0x12f, 0xb, 0x3, 0x2, 0x2, 0x2, 
    0x130, 0x134, 0x7, 0x59, 0x2, 0x2, 0x131, 0x133, 0x5, 0xca, 0x66, 0x2, 
    0x132, 0x131, 0x3, 0x2, 0x2, 0x2, 0x133, 0x136, 0x3, 0x2, 0x2, 0x2, 
    0x134, 0x132, 0x3, 0x2, 0x2, 0x2, 0x134, 0x135, 0x3, 0x2, 0x2, 0x2, 
    0x135, 0x137, 0x3, 0x2, 0x2, 0x2, 0x136, 0x134, 0x3, 0x2, 0x2, 0x2, 
    0x137, 0x138, 0x7, 0x51, 0x2, 0x2, 0x138, 0xd, 0x3, 0x2, 0x2, 0x2, 0x139, 
    0x13b, 0x5, 0xbe, 0x60, 0x2, 0x13a, 0x139, 0x3, 0x2, 0x2, 0x2, 0x13b, 
    0x13e, 0x3, 0x2, 0x2, 0x2, 0x13c, 0x13a, 0x3, 0x2, 0x2, 0x2, 0x13c, 
    0x13d, 0x3, 0x2, 0x2, 0x2, 0x13d, 0x148, 0x3, 0x2, 0x2, 0x2, 0x13e, 
    0x13c, 0x3, 0x2, 0x2, 0x2, 0x13f, 0x143, 0x7, 0x57, 0x2, 0x2, 0x140, 
    0x142, 0x5, 0xbe, 0x60, 0x2, 0x141, 0x140, 0x3, 0x2, 0x2, 0x2, 0x142, 
    0x145, 0x3, 0x2, 0x2, 0x2, 0x143, 0x141, 0x3, 0x2, 0x2, 0x2, 0x143, 
    0x144, 0x3, 0x2, 0x2, 0x2, 0x144, 0x147, 0x3, 0x2, 0x2, 0x2, 0x145, 
    0x143, 0x3, 0x2, 0x2, 0x2, 0x146, 0x13f, 0x3, 0x2, 0x2, 0x2, 0x147, 
    0x14a, 0x3, 0x2, 0x2, 0x2, 0x148, 0x146, 0x3, 0x2, 0x2, 0x2, 0x148, 
    0x149, 0x3, 0x2, 0x2, 0x2, 0x149, 0xf, 0x3, 0x2, 0x2, 0x2, 0x14a, 0x148, 
    0x3, 0x2, 0x2, 0x2, 0x14b, 0x14c, 0x9, 0x3, 0x2, 0x2, 0x14c, 0x11, 0x3, 
    0x2, 0x2, 0x2, 0x14d, 0x14e, 0x7, 0x4d, 0x2, 0x2, 0x14e, 0x13, 0x3, 
    0x2, 0x2, 0x2, 0x14f, 0x150, 0x7, 0x4b, 0x2, 0x2, 0x150, 0x15, 0x3, 
    0x2, 0x2, 0x2, 0x151, 0x152, 0x7, 0x4a, 0x2, 0x2, 0x152, 0x17, 0x3, 
    0x2, 0x2, 0x2, 0x153, 0x159, 0x5, 0x9e, 0x50, 0x2, 0x154, 0x159, 0x5, 
    0xa2, 0x52, 0x2, 0x155, 0x159, 0x5, 0xa4, 0x53, 0x2, 0x156, 0x159, 0x5, 
    0xa0, 0x51, 0x2, 0x157, 0x159, 0x5, 0xa6, 0x54, 0x2, 0x158, 0x153, 0x3, 
    0x2, 0x2, 0x2, 0x158, 0x154, 0x3, 0x2, 0x2, 0x2, 0x158, 0x155, 0x3, 
    0x2, 0x2, 0x2, 0x158, 0x156, 0x3, 0x2, 0x2, 0x2, 0x158, 0x157, 0x3, 
    0x2, 0x2, 0x2, 0x159, 0x19, 0x3, 0x2, 0x2, 0x2, 0x15a, 0x15b, 0x7, 0x11, 
    0x2, 0x2, 0x15b, 0x160, 0x7, 0x49, 0x2, 0x2, 0x15c, 0x161, 0x7, 0x47, 
    0x2, 0x2, 0x15d, 0x161, 0x7, 0x48, 0x2, 0x2, 0x15e, 0x161, 0x7, 0x5a, 
    0x2, 0x2, 0x15f, 0x161, 0x5, 0xa, 0x6, 0x2, 0x160, 0x15c, 0x3, 0x2, 
    0x2, 0x2, 0x160, 0x15d, 0x3, 0x2, 0x2, 0x2, 0x160, 0x15e, 0x3, 0x2, 
    0x2, 0x2, 0x160, 0x15f, 0x3, 0x2, 0x2, 0x2, 0x161, 0x1b, 0x3, 0x2, 0x2, 
    0x2, 0x162, 0x163, 0x7, 0x19, 0x2, 0x2, 0x163, 0x164, 0x7, 0x49, 0x2, 
    0x2, 0x164, 0x165, 0x5, 0x12, 0xa, 0x2, 0x165, 0x166, 0x7, 0x47, 0x2, 
    0x2, 0x166, 0x167, 0x7, 0x49, 0x2, 0x2, 0x167, 0x168, 0x5, 0x12, 0xa, 
    0x2, 0x168, 0x1d, 0x3, 0x2, 0x2, 0x2, 0x169, 0x16a, 0x7, 0x9, 0x2, 0x2, 
    0x16a, 0x16b, 0x7, 0x49, 0x2, 0x2, 0x16b, 0x16c, 0x7, 0x48, 0x2, 0x2, 
    0x16c, 0x1f, 0x3, 0x2, 0x2, 0x2, 0x16d, 0x16e, 0x7, 0x35, 0x2, 0x2, 
    0x16e, 0x21, 0x3, 0x2, 0x2, 0x2, 0x16f, 0x170, 0x7, 0x36, 0x2, 0x2, 
    0x170, 0x23, 0x3, 0x2, 0x2, 0x2, 0x171, 0x172, 0x7, 0x16, 0x2, 0x2, 
    0x172, 0x173, 0x7, 0x4c, 0x2, 0x2, 0x173, 0x25, 0x3, 0x2, 0x2, 0x2, 
    0x174, 0x175, 0x7, 0xa, 0x2, 0x2, 0x175, 0x179, 0x7, 0x49, 0x2, 0x2, 
    0x176, 0x17a, 0x7, 0x48, 0x2, 0x2, 0x177, 0x17a, 0x7, 0x5a, 0x2, 0x2, 
    0x178, 0x17a, 0x5, 0xa, 0x6, 0x2, 0x179, 0x176, 0x3, 0x2, 0x2, 0x2, 
    0x179, 0x177, 0x3, 0x2, 0x2, 0x2, 0x179, 0x178, 0x3, 0x2, 0x2, 0x2, 
    0x17a, 0x27, 0x3, 0x2, 0x2, 0x2, 0x17b, 0x17c, 0x7, 0xb, 0x2, 0x2, 0x17c, 
    0x180, 0x7, 0x49, 0x2, 0x2, 0x17d, 0x181, 0x7, 0x48, 0x2, 0x2, 0x17e, 
    0x181, 0x7, 0x5a, 0x2, 0x2, 0x17f, 0x181, 0x5, 0xa, 0x6, 0x2, 0x180, 
    0x17d, 0x3, 0x2, 0x2, 0x2, 0x180, 0x17e, 0x3, 0x2, 0x2, 0x2, 0x180, 
    0x17f, 0x3, 0x2, 0x2, 0x2, 0x181, 0x29, 0x3, 0x2, 0x2, 0x2, 0x182, 0x183, 
    0x7, 0xb, 0x2, 0x2, 0x183, 0x187, 0x7, 0x49, 0x2, 0x2, 0x184, 0x188, 
    0x5, 0xa8, 0x55, 0x2, 0x185, 0x188, 0x7, 0x5a, 0x2, 0x2, 0x186, 0x188, 
    0x5, 0xa, 0x6, 0x2, 0x187, 0x184, 0x3, 0x2, 0x2, 0x2, 0x187, 0x185, 
    0x3, 0x2, 0x2, 0x2, 0x187, 0x186, 0x3, 0x2, 0x2, 0x2, 0x188, 0x2b, 0x3, 
    0x2, 0x2, 0x2, 0x189, 0x18a, 0x7, 0xc, 0x2, 0x2, 0x18a, 0x18e, 0x7, 
    0x49, 0x2, 0x2, 0x18b, 0x18f, 0x7, 0x48, 0x2, 0x2, 0x18c, 0x18f, 0x7, 
    0x5a, 0x2, 0x2, 0x18d, 0x18f, 0x5, 0xa, 0x6, 0x2, 0x18e, 0x18b, 0x3, 
    0x2, 0x2, 0x2, 0x18e, 0x18c, 0x3, 0x2, 0x2, 0x2, 0x18e, 0x18d, 0x3, 
    0x2, 0x2, 0x2, 0x18f, 0x2d, 0x3, 0x2, 0x2, 0x2, 0x190, 0x191, 0x7, 0xc, 
    0x2, 0x2, 0x191, 0x195, 0x7, 0x49, 0x2, 0x2, 0x192, 0x196, 0x5, 0xa8, 
    0x55, 0x2, 0x193, 0x196, 0x7, 0x5a, 0x2, 0x2, 0x194, 0x196, 0x5, 0xa, 
    0x6, 0x2, 0x195, 0x192, 0x3, 0x2, 0x2, 0x2, 0x195, 0x193, 0x3, 0x2, 
    0x2, 0x2, 0x195, 0x194, 0x3, 0x2, 0x2, 0x2, 0x196, 0x2f, 0x3, 0x2, 0x2, 
    0x2, 0x197, 0x198, 0x7, 0xe, 0x2, 0x2, 0x198, 0x19c, 0x7, 0x49, 0x2, 
    0x2, 0x199, 0x19d, 0x7, 0x48, 0x2, 0x2, 0x19a, 0x19d, 0x7, 0x5a, 0x2, 
    0x2, 0x19b, 0x19d, 0x5, 0xa, 0x6, 0x2, 0x19c, 0x199, 0x3, 0x2, 0x2, 
    0x2, 0x19c, 0x19a, 0x3, 0x2, 0x2, 0x2, 0x19c, 0x19b, 0x3, 0x2, 0x2, 
    0x2, 0x19d, 0x31, 0x3, 0x2, 0x2, 0x2, 0x19e, 0x19f, 0x7, 0xe, 0x2, 0x2, 
    0x19f, 0x1a3, 0x7, 0x49, 0x2, 0x2, 0x1a0, 0x1a4, 0x5, 0xa8, 0x55, 0x2, 
    0x1a1, 0x1a4, 0x7, 0x5a, 0x2, 0x2, 0x1a2, 0x1a4, 0x5, 0xa, 0x6, 0x2, 
    0x1a3, 0x1a0, 0x3, 0x2, 0x2, 0x2, 0x1a3, 0x1a1, 0x3, 0x2, 0x2, 0x2, 
    0x1a3, 0x1a2, 0x3, 0x2, 0x2, 0x2, 0x1a4, 0x33, 0x3, 0x2, 0x2, 0x2, 0x1a5, 
    0x1a6, 0x7, 0xf, 0x2, 0x2, 0x1a6, 0x1aa, 0x7, 0x49, 0x2, 0x2, 0x1a7, 
    0x1ab, 0x7, 0x48, 0x2, 0x2, 0x1a8, 0x1ab, 0x7, 0x5a, 0x2, 0x2, 0x1a9, 
    0x1ab, 0x5, 0xa, 0x6, 0x2, 0x1aa, 0x1a7, 0x3, 0x2, 0x2, 0x2, 0x1aa, 
    0x1a8, 0x3, 0x2, 0x2, 0x2, 0x1aa, 0x1a9, 0x3, 0x2, 0x2, 0x2, 0x1ab, 
    0x35, 0x3, 0x2, 0x2, 0x2, 0x1ac, 0x1ad, 0x7, 0xf, 0x2, 0x2, 0x1ad, 0x1b1, 
    0x7, 0x49, 0x2, 0x2, 0x1ae, 0x1b2, 0x5, 0xa8, 0x55, 0x2, 0x1af, 0x1b2, 
    0x7, 0x5a, 0x2, 0x2, 0x1b0, 0x1b2, 0x5, 0xa, 0x6, 0x2, 0x1b1, 0x1ae, 
    0x3, 0x2, 0x2, 0x2, 0x1b1, 0x1af, 0x3, 0x2, 0x2, 0x2, 0x1b1, 0x1b0, 
    0x3, 0x2, 0x2, 0x2, 0x1b2, 0x37, 0x3, 0x2, 0x2, 0x2, 0x1b3, 0x1b4, 0x7, 
    0xd, 0x2, 0x2, 0x1b4, 0x39, 0x3, 0x2, 0x2, 0x2, 0x1b5, 0x1b9, 0x7, 0x10, 
    0x2, 0x2, 0x1b6, 0x1b8, 0x7, 0x49, 0x2, 0x2, 0x1b7, 0x1b6, 0x3, 0x2, 
    0x2, 0x2, 0x1b8, 0x1bb, 0x3, 0x2, 0x2, 0x2, 0x1b9, 0x1b7, 0x3, 0x2, 
    0x2, 0x2, 0x1b9, 0x1ba, 0x3, 0x2, 0x2, 0x2, 0x1ba, 0x1bc, 0x3, 0x2, 
    0x2, 0x2, 0x1bb, 0x1b9, 0x3, 0x2, 0x2, 0x2, 0x1bc, 0x1bf, 0x7, 0x3, 
    0x2, 0x2, 0x1bd, 0x1bf, 0x7, 0x10, 0x2, 0x2, 0x1be, 0x1b5, 0x3, 0x2, 
    0x2, 0x2, 0x1be, 0x1bd, 0x3, 0x2, 0x2, 0x2, 0x1bf, 0x3b, 0x3, 0x2, 0x2, 
    0x2, 0x1c0, 0x1c1, 0x7, 0x15, 0x2, 0x2, 0x1c1, 0x3d, 0x3, 0x2, 0x2, 
    0x2, 0x1c2, 0x1c3, 0x7, 0x13, 0x2, 0x2, 0x1c3, 0x1c4, 0x7, 0x49, 0x2, 
    0x2, 0x1c4, 0x1c5, 0x7, 0x47, 0x2, 0x2, 0x1c5, 0x3f, 0x3, 0x2, 0x2, 
    0x2, 0x1c6, 0x1c7, 0x7, 0x14, 0x2, 0x2, 0x1c7, 0x41, 0x3, 0x2, 0x2, 
    0x2, 0x1c8, 0x1c9, 0x7, 0x12, 0x2, 0x2, 0x1c9, 0x1ca, 0x7, 0x49, 0x2, 
    0x2, 0x1ca, 0x1d5, 0x7, 0x48, 0x2, 0x2, 0x1cb, 0x1d0, 0x5, 0xbc, 0x5f, 
    0x2, 0x1cc, 0x1cd, 0x7, 0x5f, 0x2, 0x2, 0x1cd, 0x1cf, 0x5, 0xbc, 0x5f, 
    0x2, 0x1ce, 0x1cc, 0x3, 0x2, 0x2, 0x2, 0x1cf, 0x1d2, 0x3, 0x2, 0x2, 
    0x2, 0x1d0, 0x1ce, 0x3, 0x2, 0x2, 0x2, 0x1d0, 0x1d1, 0x3, 0x2, 0x2, 
    0x2, 0x1d1, 0x1d4, 0x3, 0x2, 0x2, 0x2, 0x1d2, 0x1d0, 0x3, 0x2, 0x2, 
    0x2, 0x1d3, 0x1cb, 0x3, 0x2, 0x2, 0x2, 0x1d4, 0x1d7, 0x3, 0x2, 0x2, 
    0x2, 0x1d5, 0x1d3, 0x3, 0x2, 0x2, 0x2, 0x1d5, 0x1d6, 0x3, 0x2, 0x2, 
    0x2, 0x1d6, 0x43, 0x3, 0x2, 0x2, 0x2, 0x1d7, 0x1d5, 0x3, 0x2, 0x2, 0x2, 
    0x1d8, 0x1dc, 0x7, 0x7, 0x2, 0x2, 0x1d9, 0x1db, 0x7, 0x49, 0x2, 0x2, 
    0x1da, 0x1d9, 0x3, 0x2, 0x2, 0x2, 0x1db, 0x1de, 0x3, 0x2, 0x2, 0x2, 
    0x1dc, 0x1da, 0x3, 0x2, 0x2, 0x2, 0x1dc, 0x1dd, 0x3, 0x2, 0x2, 0x2, 
    0x1dd, 0x1df, 0x3, 0x2, 0x2, 0x2, 0x1de, 0x1dc, 0x3, 0x2, 0x2, 0x2, 
    0x1df, 0x1e0, 0x7, 0x51, 0x2, 0x2, 0x1e0, 0x45, 0x3, 0x2, 0x2, 0x2, 
    0x1e1, 0x1e5, 0x7, 0x8, 0x2, 0x2, 0x1e2, 0x1e4, 0x7, 0x49, 0x2, 0x2, 
    0x1e3, 0x1e2, 0x3, 0x2, 0x2, 0x2, 0x1e4, 0x1e7, 0x3, 0x2, 0x2, 0x2, 
    0x1e5, 0x1e3, 0x3, 0x2, 0x2, 0x2, 0x1e5, 0x1e6, 0x3, 0x2, 0x2, 0x2, 
    0x1e6, 0x1e8, 0x3, 0x2, 0x2, 0x2, 0x1e7, 0x1e5, 0x3, 0x2, 0x2, 0x2, 
    0x1e8, 0x1e9, 0x7, 0x51, 0x2, 0x2, 0x1e9, 0x47, 0x3, 0x2, 0x2, 0x2, 
    0x1ea, 0x1ee, 0x7, 0x23, 0x2, 0x2, 0x1eb, 0x1ed, 0x7, 0x49, 0x2, 0x2, 
    0x1ec, 0x1eb, 0x3, 0x2, 0x2, 0x2, 0x1ed, 0x1f0, 0x3, 0x2, 0x2, 0x2, 
    0x1ee, 0x1ec, 0x3, 0x2, 0x2, 0x2, 0x1ee, 0x1ef, 0x3, 0x2, 0x2, 0x2, 
    0x1ef, 0x1f1, 0x3, 0x2, 0x2, 0x2, 0x1f0, 0x1ee, 0x3, 0x2, 0x2, 0x2, 
    0x1f1, 0x1f2, 0x7, 0x51, 0x2, 0x2, 0x1f2, 0x49, 0x3, 0x2, 0x2, 0x2, 
    0x1f3, 0x1f7, 0x7, 0x2b, 0x2, 0x2, 0x1f4, 0x1f6, 0x7, 0x49, 0x2, 0x2, 
    0x1f5, 0x1f4, 0x3, 0x2, 0x2, 0x2, 0x1f6, 0x1f9, 0x3, 0x2, 0x2, 0x2, 
    0x1f7, 0x1f5, 0x3, 0x2, 0x2, 0x2, 0x1f7, 0x1f8, 0x3, 0x2, 0x2, 0x2, 
    0x1f8, 0x1fa, 0x3, 0x2, 0x2, 0x2, 0x1f9, 0x1f7, 0x3, 0x2, 0x2, 0x2, 
    0x1fa, 0x1fb, 0x7, 0x51, 0x2, 0x2, 0x1fb, 0x4b, 0x3, 0x2, 0x2, 0x2, 
    0x1fc, 0x1fd, 0x7, 0x2c, 0x2, 0x2, 0x1fd, 0x4d, 0x3, 0x2, 0x2, 0x2, 
    0x1fe, 0x1ff, 0x7, 0x2d, 0x2, 0x2, 0x1ff, 0x4f, 0x3, 0x2, 0x2, 0x2, 
    0x200, 0x201, 0x7, 0x2e, 0x2, 0x2, 0x201, 0x51, 0x3, 0x2, 0x2, 0x2, 
    0x202, 0x203, 0x7, 0x2f, 0x2, 0x2, 0x203, 0x53, 0x3, 0x2, 0x2, 0x2, 
    0x204, 0x205, 0x7, 0x30, 0x2, 0x2, 0x205, 0x55, 0x3, 0x2, 0x2, 0x2, 
    0x206, 0x208, 0x7, 0x24, 0x2, 0x2, 0x207, 0x209, 0x5, 0xc2, 0x62, 0x2, 
    0x208, 0x207, 0x3, 0x2, 0x2, 0x2, 0x209, 0x20a, 0x3, 0x2, 0x2, 0x2, 
    0x20a, 0x208, 0x3, 0x2, 0x2, 0x2, 0x20a, 0x20b, 0x3, 0x2, 0x2, 0x2, 
    0x20b, 0x57, 0x3, 0x2, 0x2, 0x2, 0x20c, 0x20d, 0x7, 0x25, 0x2, 0x2, 
    0x20d, 0x59, 0x3, 0x2, 0x2, 0x2, 0x20e, 0x20f, 0x7, 0x26, 0x2, 0x2, 
    0x20f, 0x5b, 0x3, 0x2, 0x2, 0x2, 0x210, 0x211, 0x7, 0x27, 0x2, 0x2, 
    0x211, 0x5d, 0x3, 0x2, 0x2, 0x2, 0x212, 0x213, 0x7, 0x28, 0x2, 0x2, 
    0x213, 0x5f, 0x3, 0x2, 0x2, 0x2, 0x214, 0x215, 0x7, 0x29, 0x2, 0x2, 
    0x215, 0x61, 0x3, 0x2, 0x2, 0x2, 0x216, 0x217, 0x7, 0x2a, 0x2, 0x2, 
    0x217, 0x63, 0x3, 0x2, 0x2, 0x2, 0x218, 0x219, 0x7, 0x31, 0x2, 0x2, 
    0x219, 0x65, 0x3, 0x2, 0x2, 0x2, 0x21a, 0x21b, 0x7, 0x32, 0x2, 0x2, 
    0x21b, 0x67, 0x3, 0x2, 0x2, 0x2, 0x21c, 0x21d, 0x7, 0x33, 0x2, 0x2, 
    0x21d, 0x69, 0x3, 0x2, 0x2, 0x2, 0x21e, 0x21f, 0x7, 0x34, 0x2, 0x2, 
    0x21f, 0x6b, 0x3, 0x2, 0x2, 0x2, 0x220, 0x221, 0x7, 0x21, 0x2, 0x2, 
    0x221, 0x6d, 0x3, 0x2, 0x2, 0x2, 0x222, 0x223, 0x7, 0x22, 0x2, 0x2, 
    0x223, 0x6f, 0x3, 0x2, 0x2, 0x2, 0x224, 0x225, 0x7, 0x1b, 0x2, 0x2, 
    0x225, 0x226, 0x7, 0x49, 0x2, 0x2, 0x226, 0x227, 0x5, 0x12, 0xa, 0x2, 
    0x227, 0x71, 0x3, 0x2, 0x2, 0x2, 0x228, 0x229, 0x7, 0x1a, 0x2, 0x2, 
    0x229, 0x22d, 0x7, 0x49, 0x2, 0x2, 0x22a, 0x22e, 0x5, 0x12, 0xa, 0x2, 
    0x22b, 0x22e, 0x7, 0x48, 0x2, 0x2, 0x22c, 0x22e, 0x7, 0x4e, 0x2, 0x2, 
    0x22d, 0x22a, 0x3, 0x2, 0x2, 0x2, 0x22d, 0x22b, 0x3, 0x2, 0x2, 0x2, 
    0x22d, 0x22c, 0x3, 0x2, 0x2, 0x2, 0x22e, 0x73, 0x3, 0x2, 0x2, 0x2, 0x22f, 
    0x230, 0x7, 0x17, 0x2, 0x2, 0x230, 0x231, 0x7, 0x49, 0x2, 0x2, 0x231, 
    0x232, 0x7, 0x48, 0x2, 0x2, 0x232, 0x75, 0x3, 0x2, 0x2, 0x2, 0x233, 
    0x237, 0x7, 0x18, 0x2, 0x2, 0x234, 0x236, 0x7, 0x49, 0x2, 0x2, 0x235, 
    0x234, 0x3, 0x2, 0x2, 0x2, 0x236, 0x239, 0x3, 0x2, 0x2, 0x2, 0x237, 
    0x235, 0x3, 0x2, 0x2, 0x2, 0x237, 0x238, 0x3, 0x2, 0x2, 0x2, 0x238, 
    0x23a, 0x3, 0x2, 0x2, 0x2, 0x239, 0x237, 0x3, 0x2, 0x2, 0x2, 0x23a, 
    0x23b, 0x7, 0x51, 0x2, 0x2, 0x23b, 0x77, 0x3, 0x2, 0x2, 0x2, 0x23c, 
    0x23d, 0x7, 0x1c, 0x2, 0x2, 0x23d, 0x79, 0x3, 0x2, 0x2, 0x2, 0x23e, 
    0x23f, 0x7, 0x1d, 0x2, 0x2, 0x23f, 0x7b, 0x3, 0x2, 0x2, 0x2, 0x240, 
    0x241, 0x7, 0x1e, 0x2, 0x2, 0x241, 0x7d, 0x3, 0x2, 0x2, 0x2, 0x242, 
    0x243, 0x7, 0x1f, 0x2, 0x2, 0x243, 0x7f, 0x3, 0x2, 0x2, 0x2, 0x244, 
    0x245, 0x7, 0x20, 0x2, 0x2, 0x245, 0x81, 0x3, 0x2, 0x2, 0x2, 0x246, 
    0x247, 0x7, 0x37, 0x2, 0x2, 0x247, 0x83, 0x3, 0x2, 0x2, 0x2, 0x248, 
    0x249, 0x7, 0x38, 0x2, 0x2, 0x249, 0x85, 0x3, 0x2, 0x2, 0x2, 0x24a, 
    0x24b, 0x7, 0x39, 0x2, 0x2, 0x24b, 0x87, 0x3, 0x2, 0x2, 0x2, 0x24c, 
    0x24d, 0x7, 0x3a, 0x2, 0x2, 0x24d, 0x89, 0x3, 0x2, 0x2, 0x2, 0x24e, 
    0x24f, 0x7, 0x3b, 0x2, 0x2, 0x24f, 0x8b, 0x3, 0x2, 0x2, 0x2, 0x250, 
    0x251, 0x7, 0x3c, 0x2, 0x2, 0x251, 0x8d, 0x3, 0x2, 0x2, 0x2, 0x252, 
    0x253, 0x7, 0x3d, 0x2, 0x2, 0x253, 0x8f, 0x3, 0x2, 0x2, 0x2, 0x254, 
    0x255, 0x7, 0x3e, 0x2, 0x2, 0x255, 0x91, 0x3, 0x2, 0x2, 0x2, 0x256, 
    0x257, 0x7, 0x3f, 0x2, 0x2, 0x257, 0x93, 0x3, 0x2, 0x2, 0x2, 0x258, 
    0x259, 0x7, 0x40, 0x2, 0x2, 0x259, 0x95, 0x3, 0x2, 0x2, 0x2, 0x25a, 
    0x25b, 0x7, 0x41, 0x2, 0x2, 0x25b, 0x97, 0x3, 0x2, 0x2, 0x2, 0x25c, 
    0x25d, 0x7, 0x42, 0x2, 0x2, 0x25d, 0x99, 0x3, 0x2, 0x2, 0x2, 0x25e, 
    0x25f, 0x7, 0x43, 0x2, 0x2, 0x25f, 0x9b, 0x3, 0x2, 0x2, 0x2, 0x260, 
    0x261, 0x7, 0x44, 0x2, 0x2, 0x261, 0x9d, 0x3, 0x2, 0x2, 0x2, 0x262, 
    0x263, 0x7, 0x6, 0x2, 0x2, 0x263, 0x264, 0x7, 0x49, 0x2, 0x2, 0x264, 
    0x268, 0x9, 0x4, 0x2, 0x2, 0x265, 0x267, 0x7, 0x49, 0x2, 0x2, 0x266, 
    0x265, 0x3, 0x2, 0x2, 0x2, 0x267, 0x26a, 0x3, 0x2, 0x2, 0x2, 0x268, 
    0x266, 0x3, 0x2, 0x2, 0x2, 0x268, 0x269, 0x3, 0x2, 0x2, 0x2, 0x269, 
    0x26b, 0x3, 0x2, 0x2, 0x2, 0x26a, 0x268, 0x3, 0x2, 0x2, 0x2, 0x26b, 
    0x26c, 0x7, 0x51, 0x2, 0x2, 0x26c, 0x9f, 0x3, 0x2, 0x2, 0x2, 0x26d, 
    0x26e, 0x7, 0x6, 0x2, 0x2, 0x26e, 0x26f, 0x7, 0x49, 0x2, 0x2, 0x26f, 
    0x273, 0x9, 0x4, 0x2, 0x2, 0x270, 0x272, 0x7, 0x49, 0x2, 0x2, 0x271, 
    0x270, 0x3, 0x2, 0x2, 0x2, 0x272, 0x275, 0x3, 0x2, 0x2, 0x2, 0x273, 
    0x271, 0x3, 0x2, 0x2, 0x2, 0x273, 0x274, 0x3, 0x2, 0x2, 0x2, 0x274, 
    0x276, 0x3, 0x2, 0x2, 0x2, 0x275, 0x273, 0x3, 0x2, 0x2, 0x2, 0x276, 
    0x277, 0x5, 0xb2, 0x5a, 0x2, 0x277, 0xa1, 0x3, 0x2, 0x2, 0x2, 0x278, 
    0x279, 0x7, 0x6, 0x2, 0x2, 0x279, 0x27a, 0x7, 0x49, 0x2, 0x2, 0x27a, 
    0x27b, 0x9, 0x4, 0x2, 0x2, 0x27b, 0x27f, 0x5, 0xb0, 0x59, 0x2, 0x27c, 
    0x27e, 0x7, 0x49, 0x2, 0x2, 0x27d, 0x27c, 0x3, 0x2, 0x2, 0x2, 0x27e, 
    0x281, 0x3, 0x2, 0x2, 0x2, 0x27f, 0x27d, 0x3, 0x2, 0x2, 0x2, 0x27f, 
    0x280, 0x3, 0x2, 0x2, 0x2, 0x280, 0x282, 0x3, 0x2, 0x2, 0x2, 0x281, 
    0x27f, 0x3, 0x2, 0x2, 0x2, 0x282, 0x283, 0x5, 0xb2, 0x5a, 0x2, 0x283, 
    0xa3, 0x3, 0x2, 0x2, 0x2, 0x284, 0x285, 0x7, 0x6, 0x2, 0x2, 0x285, 0x286, 
    0x7, 0x49, 0x2, 0x2, 0x286, 0x287, 0x9, 0x4, 0x2, 0x2, 0x287, 0x288, 
    0x7, 0x49, 0x2, 0x2, 0x288, 0x289, 0x5, 0xb8, 0x5d, 0x2, 0x289, 0x28a, 
    0x9, 0x5, 0x2, 0x2, 0x28a, 0x296, 0x3, 0x2, 0x2, 0x2, 0x28b, 0x28c, 
    0x7, 0x6, 0x2, 0x2, 0x28c, 0x28d, 0x7, 0x49, 0x2, 0x2, 0x28d, 0x291, 
    0x9, 0x4, 0x2, 0x2, 0x28e, 0x290, 0x7, 0x49, 0x2, 0x2, 0x28f, 0x28e, 
    0x3, 0x2, 0x2, 0x2, 0x290, 0x293, 0x3, 0x2, 0x2, 0x2, 0x291, 0x28f, 
    0x3, 0x2, 0x2, 0x2, 0x291, 0x292, 0x3, 0x2, 0x2, 0x2, 0x292, 0x294, 
    0x3, 0x2, 0x2, 0x2, 0x293, 0x291, 0x3, 0x2, 0x2, 0x2, 0x294, 0x296, 
    0x7, 0x51, 0x2, 0x2, 0x295, 0x284, 0x3, 0x2, 0x2, 0x2, 0x295, 0x28b, 
    0x3, 0x2, 0x2, 0x2, 0x296, 0xa5, 0x3, 0x2, 0x2, 0x2, 0x297, 0x298, 0x7, 
    0x6, 0x2, 0x2, 0x298, 0x299, 0x7, 0x49, 0x2, 0x2, 0x299, 0x29a, 0x9, 
    0x4, 0x2, 0x2, 0x29a, 0x29b, 0x5, 0xb0, 0x59, 0x2, 0x29b, 0x29c, 0x7, 
    0x49, 0x2, 0x2, 0x29c, 0x29d, 0x5, 0xb8, 0x5d, 0x2, 0x29d, 0x29e, 0x9, 
    0x5, 0x2, 0x2, 0x29e, 0x2ac, 0x3, 0x2, 0x2, 0x2, 0x29f, 0x2a0, 0x7, 
    0x6, 0x2, 0x2, 0x2a0, 0x2a1, 0x7, 0x49, 0x2, 0x2, 0x2a1, 0x2a2, 0x9, 
    0x4, 0x2, 0x2, 0x2a2, 0x2a6, 0x5, 0xb0, 0x59, 0x2, 0x2a3, 0x2a5, 0x7, 
    0x49, 0x2, 0x2, 0x2a4, 0x2a3, 0x3, 0x2, 0x2, 0x2, 0x2a5, 0x2a8, 0x3, 
    0x2, 0x2, 0x2, 0x2a6, 0x2a4, 0x3, 0x2, 0x2, 0x2, 0x2a6, 0x2a7, 0x3, 
    0x2, 0x2, 0x2, 0x2a7, 0x2a9, 0x3, 0x2, 0x2, 0x2, 0x2a8, 0x2a6, 0x3, 
    0x2, 0x2, 0x2, 0x2a9, 0x2aa, 0x7, 0x51, 0x2, 0x2, 0x2aa, 0x2ac, 0x3, 
    0x2, 0x2, 0x2, 0x2ab, 0x297, 0x3, 0x2, 0x2, 0x2, 0x2ab, 0x29f, 0x3, 
    0x2, 0x2, 0x2, 0x2ac, 0xa7, 0x3, 0x2, 0x2, 0x2, 0x2ad, 0x2af, 0x7, 0x48, 
    0x2, 0x2, 0x2ae, 0x2b0, 0x7, 0x54, 0x2, 0x2, 0x2af, 0x2ae, 0x3, 0x2, 
    0x2, 0x2, 0x2af, 0x2b0, 0x3, 0x2, 0x2, 0x2, 0x2b0, 0x2b2, 0x3, 0x2, 
    0x2, 0x2, 0x2b1, 0x2ad, 0x3, 0x2, 0x2, 0x2, 0x2b2, 0x2b5, 0x3, 0x2, 
    0x2, 0x2, 0x2b3, 0x2b1, 0x3, 0x2, 0x2, 0x2, 0x2b3, 0x2b4, 0x3, 0x2, 
    0x2, 0x2, 0x2b4, 0xa9, 0x3, 0x2, 0x2, 0x2, 0x2b5, 0x2b3, 0x3, 0x2, 0x2, 
    0x2, 0x2b6, 0x2b7, 0x7, 0x6, 0x2, 0x2, 0x2b7, 0x2ba, 0x7, 0x49, 0x2, 
    0x2, 0x2b8, 0x2bb, 0x5, 0xa8, 0x55, 0x2, 0x2b9, 0x2bb, 0x7, 0x5a, 0x2, 
    0x2, 0x2ba, 0x2b8, 0x3, 0x2, 0x2, 0x2, 0x2ba, 0x2b9, 0x3, 0x2, 0x2, 
    0x2, 0x2bb, 0x2bc, 0x3, 0x2, 0x2, 0x2, 0x2bc, 0x2bd, 0x7, 0x49, 0x2, 
    0x2, 0x2bd, 0x2d3, 0x5, 0xba, 0x5e, 0x2, 0x2be, 0x2bf, 0x7, 0x6, 0x2, 
    0x2, 0x2bf, 0x2c2, 0x7, 0x49, 0x2, 0x2, 0x2c0, 0x2c3, 0x5, 0xa8, 0x55, 
    0x2, 0x2c1, 0x2c3, 0x7, 0x5a, 0x2, 0x2, 0x2c2, 0x2c0, 0x3, 0x2, 0x2, 
    0x2, 0x2c2, 0x2c1, 0x3, 0x2, 0x2, 0x2, 0x2c3, 0x2c7, 0x3, 0x2, 0x2, 
    0x2, 0x2c4, 0x2c6, 0x7, 0x49, 0x2, 0x2, 0x2c5, 0x2c4, 0x3, 0x2, 0x2, 
    0x2, 0x2c6, 0x2c9, 0x3, 0x2, 0x2, 0x2, 0x2c7, 0x2c5, 0x3, 0x2, 0x2, 
    0x2, 0x2c7, 0x2c8, 0x3, 0x2, 0x2, 0x2, 0x2c8, 0x2d3, 0x3, 0x2, 0x2, 
    0x2, 0x2c9, 0x2c7, 0x3, 0x2, 0x2, 0x2, 0x2ca, 0x2cb, 0x7, 0x6, 0x2, 
    0x2, 0x2cb, 0x2ce, 0x7, 0x49, 0x2, 0x2, 0x2cc, 0x2cf, 0x5, 0xa8, 0x55, 
    0x2, 0x2cd, 0x2cf, 0x7, 0x5a, 0x2, 0x2, 0x2ce, 0x2cc, 0x3, 0x2, 0x2, 
    0x2, 0x2ce, 0x2cd, 0x3, 0x2, 0x2, 0x2, 0x2cf, 0x2d0, 0x3, 0x2, 0x2, 
    0x2, 0x2d0, 0x2d1, 0x7, 0x5, 0x2, 0x2, 0x2d1, 0x2d3, 0x5, 0xba, 0x5e, 
    0x2, 0x2d2, 0x2b6, 0x3, 0x2, 0x2, 0x2, 0x2d2, 0x2be, 0x3, 0x2, 0x2, 
    0x2, 0x2d2, 0x2ca, 0x3, 0x2, 0x2, 0x2, 0x2d3, 0xab, 0x3, 0x2, 0x2, 0x2, 
    0x2d4, 0x2d5, 0x7, 0x6, 0x2, 0x2, 0x2d5, 0x2d8, 0x7, 0x49, 0x2, 0x2, 
    0x2d6, 0x2d9, 0x5, 0xa8, 0x55, 0x2, 0x2d7, 0x2d9, 0x7, 0x5a, 0x2, 0x2, 
    0x2d8, 0x2d6, 0x3, 0x2, 0x2, 0x2, 0x2d8, 0x2d7, 0x3, 0x2, 0x2, 0x2, 
    0x2d9, 0x2da, 0x3, 0x2, 0x2, 0x2, 0x2da, 0x2db, 0x5, 0xb0, 0x59, 0x2, 
    0x2db, 0x2dc, 0x7, 0x49, 0x2, 0x2, 0x2dc, 0x2dd, 0x5, 0xba, 0x5e, 0x2, 
    0x2dd, 0x2e6, 0x3, 0x2, 0x2, 0x2, 0x2de, 0x2df, 0x7, 0x6, 0x2, 0x2, 
    0x2df, 0x2e2, 0x7, 0x49, 0x2, 0x2, 0x2e0, 0x2e3, 0x5, 0xa8, 0x55, 0x2, 
    0x2e1, 0x2e3, 0x7, 0x5a, 0x2, 0x2, 0x2e2, 0x2e0, 0x3, 0x2, 0x2, 0x2, 
    0x2e2, 0x2e1, 0x3, 0x2, 0x2, 0x2, 0x2e3, 0x2e4, 0x3, 0x2, 0x2, 0x2, 
    0x2e4, 0x2e6, 0x5, 0xb0, 0x59, 0x2, 0x2e5, 0x2d4, 0x3, 0x2, 0x2, 0x2, 
    0x2e5, 0x2de, 0x3, 0x2, 0x2, 0x2, 0x2e6, 0xad, 0x3, 0x2, 0x2, 0x2, 0x2e7, 
    0x327, 0x5, 0x44, 0x23, 0x2, 0x2e8, 0x327, 0x5, 0x46, 0x24, 0x2, 0x2e9, 
    0x327, 0x5, 0x1e, 0x10, 0x2, 0x2ea, 0x327, 0x5, 0x26, 0x14, 0x2, 0x2eb, 
    0x327, 0x5, 0x28, 0x15, 0x2, 0x2ec, 0x327, 0x5, 0x2c, 0x17, 0x2, 0x2ed, 
    0x327, 0x5, 0x38, 0x1d, 0x2, 0x2ee, 0x327, 0x5, 0x30, 0x19, 0x2, 0x2ef, 
    0x327, 0x5, 0x34, 0x1b, 0x2, 0x2f0, 0x327, 0x5, 0x3a, 0x1e, 0x2, 0x2f1, 
    0x327, 0x5, 0x1a, 0xe, 0x2, 0x2f2, 0x327, 0x5, 0x3c, 0x1f, 0x2, 0x2f3, 
    0x327, 0x5, 0x24, 0x13, 0x2, 0x2f4, 0x327, 0x5, 0x74, 0x3b, 0x2, 0x2f5, 
    0x327, 0x5, 0x76, 0x3c, 0x2, 0x2f6, 0x327, 0x5, 0x1c, 0xf, 0x2, 0x2f7, 
    0x327, 0x5, 0x72, 0x3a, 0x2, 0x2f8, 0x327, 0x5, 0x70, 0x39, 0x2, 0x2f9, 
    0x327, 0x5, 0x78, 0x3d, 0x2, 0x2fa, 0x327, 0x5, 0x7a, 0x3e, 0x2, 0x2fb, 
    0x327, 0x5, 0x7c, 0x3f, 0x2, 0x2fc, 0x327, 0x5, 0x7e, 0x40, 0x2, 0x2fd, 
    0x327, 0x5, 0x48, 0x25, 0x2, 0x2fe, 0x327, 0x5, 0x4a, 0x26, 0x2, 0x2ff, 
    0x327, 0x5, 0x4c, 0x27, 0x2, 0x300, 0x327, 0x5, 0x4e, 0x28, 0x2, 0x301, 
    0x327, 0x5, 0x50, 0x29, 0x2, 0x302, 0x327, 0x5, 0x52, 0x2a, 0x2, 0x303, 
    0x327, 0x5, 0x54, 0x2b, 0x2, 0x304, 0x327, 0x5, 0x64, 0x33, 0x2, 0x305, 
    0x327, 0x5, 0x66, 0x34, 0x2, 0x306, 0x327, 0x5, 0x68, 0x35, 0x2, 0x307, 
    0x327, 0x5, 0x6a, 0x36, 0x2, 0x308, 0x327, 0x5, 0x6c, 0x37, 0x2, 0x309, 
    0x327, 0x5, 0x6e, 0x38, 0x2, 0x30a, 0x327, 0x5, 0x80, 0x41, 0x2, 0x30b, 
    0x327, 0x5, 0x56, 0x2c, 0x2, 0x30c, 0x327, 0x5, 0x58, 0x2d, 0x2, 0x30d, 
    0x327, 0x5, 0x5a, 0x2e, 0x2, 0x30e, 0x327, 0x5, 0x5c, 0x2f, 0x2, 0x30f, 
    0x327, 0x5, 0x5e, 0x30, 0x2, 0x310, 0x327, 0x5, 0x60, 0x31, 0x2, 0x311, 
    0x327, 0x5, 0x62, 0x32, 0x2, 0x312, 0x327, 0x5, 0x20, 0x11, 0x2, 0x313, 
    0x327, 0x5, 0x22, 0x12, 0x2, 0x314, 0x327, 0x5, 0x92, 0x4a, 0x2, 0x315, 
    0x327, 0x5, 0x94, 0x4b, 0x2, 0x316, 0x327, 0x5, 0x82, 0x42, 0x2, 0x317, 
    0x327, 0x5, 0x84, 0x43, 0x2, 0x318, 0x327, 0x5, 0x86, 0x44, 0x2, 0x319, 
    0x327, 0x5, 0x88, 0x45, 0x2, 0x31a, 0x327, 0x5, 0x8a, 0x46, 0x2, 0x31b, 
    0x327, 0x5, 0x8c, 0x47, 0x2, 0x31c, 0x327, 0x5, 0x8e, 0x48, 0x2, 0x31d, 
    0x327, 0x5, 0x90, 0x49, 0x2, 0x31e, 0x327, 0x5, 0x96, 0x4c, 0x2, 0x31f, 
    0x327, 0x5, 0x98, 0x4d, 0x2, 0x320, 0x327, 0x5, 0x9a, 0x4e, 0x2, 0x321, 
    0x327, 0x5, 0x9c, 0x4f, 0x2, 0x322, 0x327, 0x5, 0xac, 0x57, 0x2, 0x323, 
    0x327, 0x5, 0xaa, 0x56, 0x2, 0x324, 0x327, 0x5, 0x14, 0xb, 0x2, 0x325, 
    0x327, 0x5, 0x16, 0xc, 0x2, 0x326, 0x2e7, 0x3, 0x2, 0x2, 0x2, 0x326, 
    0x2e8, 0x3, 0x2, 0x2, 0x2, 0x326, 0x2e9, 0x3, 0x2, 0x2, 0x2, 0x326, 
    0x2ea, 0x3, 0x2, 0x2, 0x2, 0x326, 0x2eb, 0x3, 0x2, 0x2, 0x2, 0x326, 
    0x2ec, 0x3, 0x2, 0x2, 0x2, 0x326, 0x2ed, 0x3, 0x2, 0x2, 0x2, 0x326, 
    0x2ee, 0x3, 0x2, 0x2, 0x2, 0x326, 0x2ef, 0x3, 0x2, 0x2, 0x2, 0x326, 
    0x2f0, 0x3, 0x2, 0x2, 0x2, 0x326, 0x2f1, 0x3, 0x2, 0x2, 0x2, 0x326, 
    0x2f2, 0x3, 0x2, 0x2, 0x2, 0x326, 0x2f3, 0x3, 0x2, 0x2, 0x2, 0x326, 
    0x2f4, 0x3, 0x2, 0x2, 0x2, 0x326, 0x2f5, 0x3, 0x2, 0x2, 0x2, 0x326, 
    0x2f6, 0x3, 0x2, 0x2, 0x2, 0x326, 0x2f7, 0x3, 0x2, 0x2, 0x2, 0x326, 
    0x2f8, 0x3, 0x2, 0x2, 0x2, 0x326, 0x2f9, 0x3, 0x2, 0x2, 0x2, 0x326, 
    0x2fa, 0x3, 0x2, 0x2, 0x2, 0x326, 0x2fb, 0x3, 0x2, 0x2, 0x2, 0x326, 
    0x2fc, 0x3, 0x2, 0x2, 0x2, 0x326, 0x2fd, 0x3, 0x2, 0x2, 0x2, 0x326, 
    0x2fe, 0x3, 0x2, 0x2, 0x2, 0x326, 0x2ff, 0x3, 0x2, 0x2, 0x2, 0x326, 
    0x300, 0x3, 0x2, 0x2, 0x2, 0x326, 0x301, 0x3, 0x2, 0x2, 0x2, 0x326, 
    0x302, 0x3, 0x2, 0x2, 0x2, 0x326, 0x303, 0x3, 0x2, 0x2, 0x2, 0x326, 
    0x304, 0x3, 0x2, 0x2, 0x2, 0x326, 0x305, 0x3, 0x2, 0x2, 0x2, 0x326, 
    0x306, 0x3, 0x2, 0x2, 0x2, 0x326, 0x307, 0x3, 0x2, 0x2, 0x2, 0x326, 
    0x308, 0x3, 0x2, 0x2, 0x2, 0x326, 0x309, 0x3, 0x2, 0x2, 0x2, 0x326, 
    0x30a, 0x3, 0x2, 0x2, 0x2, 0x326, 0x30b, 0x3, 0x2, 0x2, 0x2, 0x326, 
    0x30c, 0x3, 0x2, 0x2, 0x2, 0x326, 0x30d, 0x3, 0x2, 0x2, 0x2, 0x326, 
    0x30e, 0x3, 0x2, 0x2, 0x2, 0x326, 0x30f, 0x3, 0x2, 0x2, 0x2, 0x326, 
    0x310, 0x3, 0x2, 0x2, 0x2, 0x326, 0x311, 0x3, 0x2, 0x2, 0x2, 0x326, 
    0x312, 0x3, 0x2, 0x2, 0x2, 0x326, 0x313, 0x3, 0x2, 0x2, 0x2, 0x326, 
    0x314, 0x3, 0x2, 0x2, 0x2, 0x326, 0x315, 0x3, 0x2, 0x2, 0x2, 0x326, 
    0x316, 0x3, 0x2, 0x2, 0x2, 0x326, 0x317, 0x3, 0x2, 0x2, 0x2, 0x326, 
    0x318, 0x3, 0x2, 0x2, 0x2, 0x326, 0x319, 0x3, 0x2, 0x2, 0x2, 0x326, 
    0x31a, 0x3, 0x2, 0x2, 0x2, 0x326, 0x31b, 0x3, 0x2, 0x2, 0x2, 0x326, 
    0x31c, 0x3, 0x2, 0x2, 0x2, 0x326, 0x31d, 0x3, 0x2, 0x2, 0x2, 0x326, 
    0x31e, 0x3, 0x2, 0x2, 0x2, 0x326, 0x31f, 0x3, 0x2, 0x2, 0x2, 0x326, 
    0x320, 0x3, 0x2, 0x2, 0x2, 0x326, 0x321, 0x3, 0x2, 0x2, 0x2, 0x326, 
    0x322, 0x3, 0x2, 0x2, 0x2, 0x326, 0x323, 0x3, 0x2, 0x2, 0x2, 0x326, 
    0x324, 0x3, 0x2, 0x2, 0x2, 0x326, 0x325, 0x3, 0x2, 0x2, 0x2, 0x327, 
    0xaf, 0x3, 0x2, 0x2, 0x2, 0x328, 0x35d, 0x7, 0x55, 0x2, 0x2, 0x329, 
    0x32d, 0x7, 0x48, 0x2, 0x2, 0x32a, 0x32c, 0x7, 0x49, 0x2, 0x2, 0x32b, 
    0x32a, 0x3, 0x2, 0x2, 0x2, 0x32c, 0x32f, 0x3, 0x2, 0x2, 0x2, 0x32d, 
    0x32b, 0x3, 0x2, 0x2, 0x2, 0x32d, 0x32e, 0x3, 0x2, 0x2, 0x2, 0x32e, 
    0x339, 0x3, 0x2, 0x2, 0x2, 0x32f, 0x32d, 0x3, 0x2, 0x2, 0x2, 0x330, 
    0x334, 0x7, 0x58, 0x2, 0x2, 0x331, 0x333, 0x5, 0xc8, 0x65, 0x2, 0x332, 
    0x331, 0x3, 0x2, 0x2, 0x2, 0x333, 0x336, 0x3, 0x2, 0x2, 0x2, 0x334, 
    0x332, 0x3, 0x2, 0x2, 0x2, 0x334, 0x335, 0x3, 0x2, 0x2, 0x2, 0x335, 
    0x338, 0x3, 0x2, 0x2, 0x2, 0x336, 0x334, 0x3, 0x2, 0x2, 0x2, 0x337, 
    0x330, 0x3, 0x2, 0x2, 0x2, 0x338, 0x33b, 0x3, 0x2, 0x2, 0x2, 0x339, 
    0x337, 0x3, 0x2, 0x2, 0x2, 0x339, 0x33a, 0x3, 0x2, 0x2, 0x2, 0x33a, 
    0x358, 0x3, 0x2, 0x2, 0x2, 0x33b, 0x339, 0x3, 0x2, 0x2, 0x2, 0x33c, 
    0x340, 0x7, 0x57, 0x2, 0x2, 0x33d, 0x33f, 0x7, 0x49, 0x2, 0x2, 0x33e, 
    0x33d, 0x3, 0x2, 0x2, 0x2, 0x33f, 0x342, 0x3, 0x2, 0x2, 0x2, 0x340, 
    0x33e, 0x3, 0x2, 0x2, 0x2, 0x340, 0x341, 0x3, 0x2, 0x2, 0x2, 0x341, 
    0x343, 0x3, 0x2, 0x2, 0x2, 0x342, 0x340, 0x3, 0x2, 0x2, 0x2, 0x343, 
    0x347, 0x7, 0x48, 0x2, 0x2, 0x344, 0x346, 0x7, 0x49, 0x2, 0x2, 0x345, 
    0x344, 0x3, 0x2, 0x2, 0x2, 0x346, 0x349, 0x3, 0x2, 0x2, 0x2, 0x347, 
    0x345, 0x3, 0x2, 0x2, 0x2, 0x347, 0x348, 0x3, 0x2, 0x2, 0x2, 0x348, 
    0x353, 0x3, 0x2, 0x2, 0x2, 0x349, 0x347, 0x3, 0x2, 0x2, 0x2, 0x34a, 
    0x34e, 0x7, 0x58, 0x2, 0x2, 0x34b, 0x34d, 0x5, 0xc8, 0x65, 0x2, 0x34c, 
    0x34b, 0x3, 0x2, 0x2, 0x2, 0x34d, 0x350, 0x3, 0x2, 0x2, 0x2, 0x34e, 
    0x34c, 0x3, 0x2, 0x2, 0x2, 0x34e, 0x34f, 0x3, 0x2, 0x2, 0x2, 0x34f, 
    0x352, 0x3, 0x2, 0x2, 0x2, 0x350, 0x34e, 0x3, 0x2, 0x2, 0x2, 0x351, 
    0x34a, 0x3, 0x2, 0x2, 0x2, 0x352, 0x355, 0x3, 0x2, 0x2, 0x2, 0x353, 
    0x351, 0x3, 0x2, 0x2, 0x2, 0x353, 0x354, 0x3, 0x2, 0x2, 0x2, 0x354, 
    0x357, 0x3, 0x2, 0x2, 0x2, 0x355, 0x353, 0x3, 0x2, 0x2, 0x2, 0x356, 
    0x33c, 0x3, 0x2, 0x2, 0x2, 0x357, 0x35a, 0x3, 0x2, 0x2, 0x2, 0x358, 
    0x356, 0x3, 0x2, 0x2, 0x2, 0x358, 0x359, 0x3, 0x2, 0x2, 0x2, 0x359, 
    0x35c, 0x3, 0x2, 0x2, 0x2, 0x35a, 0x358, 0x3, 0x2, 0x2, 0x2, 0x35b, 
    0x329, 0x3, 0x2, 0x2, 0x2, 0x35c, 0x35f, 0x3, 0x2, 0x2, 0x2, 0x35d, 
    0x35b, 0x3, 0x2, 0x2, 0x2, 0x35d, 0x35e, 0x3, 0x2, 0x2, 0x2, 0x35e, 
    0x360, 0x3, 0x2, 0x2, 0x2, 0x35f, 0x35d, 0x3, 0x2, 0x2, 0x2, 0x360, 
    0x361, 0x7, 0x56, 0x2, 0x2, 0x361, 0xb1, 0x3, 0x2, 0x2, 0x2, 0x362, 
    0x365, 0x5, 0xb4, 0x5b, 0x2, 0x363, 0x365, 0x5, 0xb6, 0x5c, 0x2, 0x364, 
    0x362, 0x3, 0x2, 0x2, 0x2, 0x364, 0x363, 0x3, 0x2, 0x2, 0x2, 0x365, 
    0xb3, 0x3, 0x2, 0x2, 0x2, 0x366, 0x384, 0x5, 0xc, 0x7, 0x2, 0x367, 0x384, 
    0x7, 0x45, 0x2, 0x2, 0x368, 0x384, 0x7, 0x46, 0x2, 0x2, 0x369, 0x384, 
    0x5, 0xc6, 0x64, 0x2, 0x36a, 0x384, 0x7, 0x48, 0x2, 0x2, 0x36b, 0x384, 
    0x5, 0x12, 0xa, 0x2, 0x36c, 0x384, 0x7, 0x4f, 0x2, 0x2, 0x36d, 0x384, 
    0x5, 0x14, 0xb, 0x2, 0x36e, 0x384, 0x5, 0x16, 0xc, 0x2, 0x36f, 0x384, 
    0x7, 0x50, 0x2, 0x2, 0x370, 0x384, 0x7, 0x55, 0x2, 0x2, 0x371, 0x384, 
    0x7, 0x56, 0x2, 0x2, 0x372, 0x384, 0x7, 0x57, 0x2, 0x2, 0x373, 0x384, 
    0x7, 0x58, 0x2, 0x2, 0x374, 0x384, 0x7, 0x59, 0x2, 0x2, 0x375, 0x384, 
    0x7, 0x5, 0x2, 0x2, 0x376, 0x384, 0x5, 0xae, 0x58, 0x2, 0x377, 0x384, 
    0x7, 0x49, 0x2, 0x2, 0x378, 0x384, 0x7, 0x4e, 0x2, 0x2, 0x379, 0x384, 
    0x7, 0x47, 0x2, 0x2, 0x37a, 0x384, 0x5, 0x10, 0x9, 0x2, 0x37b, 0x384, 
    0x7, 0x52, 0x2, 0x2, 0x37c, 0x384, 0x7, 0x53, 0x2, 0x2, 0x37d, 0x384, 
    0x7, 0x54, 0x2, 0x2, 0x37e, 0x384, 0x7, 0x5f, 0x2, 0x2, 0x37f, 0x384, 
    0x7, 0x5b, 0x2, 0x2, 0x380, 0x384, 0x7, 0x5c, 0x2, 0x2, 0x381, 0x384, 
    0x7, 0x5d, 0x2, 0x2, 0x382, 0x384, 0x7, 0x5e, 0x2, 0x2, 0x383, 0x366, 
    0x3, 0x2, 0x2, 0x2, 0x383, 0x367, 0x3, 0x2, 0x2, 0x2, 0x383, 0x368, 
    0x3, 0x2, 0x2, 0x2, 0x383, 0x369, 0x3, 0x2, 0x2, 0x2, 0x383, 0x36a, 
    0x3, 0x2, 0x2, 0x2, 0x383, 0x36b, 0x3, 0x2, 0x2, 0x2, 0x383, 0x36c, 
    0x3, 0x2, 0x2, 0x2, 0x383, 0x36d, 0x3, 0x2, 0x2, 0x2, 0x383, 0x36e, 
    0x3, 0x2, 0x2, 0x2, 0x383, 0x36f, 0x3, 0x2, 0x2, 0x2, 0x383, 0x370, 
    0x3, 0x2, 0x2, 0x2, 0x383, 0x371, 0x3, 0x2, 0x2, 0x2, 0x383, 0x372, 
    0x3, 0x2, 0x2, 0x2, 0x383, 0x373, 0x3, 0x2, 0x2, 0x2, 0x383, 0x374, 
    0x3, 0x2, 0x2, 0x2, 0x383, 0x375, 0x3, 0x2, 0x2, 0x2, 0x383, 0x376, 
    0x3, 0x2, 0x2, 0x2, 0x383, 0x377, 0x3, 0x2, 0x2, 0x2, 0x383, 0x378, 
    0x3, 0x2, 0x2, 0x2, 0x383, 0x379, 0x3, 0x2, 0x2, 0x2, 0x383, 0x37a, 
    0x3, 0x2, 0x2, 0x2, 0x383, 0x37b, 0x3, 0x2, 0x2, 0x2, 0x383, 0x37c, 
    0x3, 0x2, 0x2, 0x2, 0x383, 0x37d, 0x3, 0x2, 0x2, 0x2, 0x383, 0x37e, 
    0x3, 0x2, 0x2, 0x2, 0x383, 0x37f, 0x3, 0x2, 0x2, 0x2, 0x383, 0x380, 
    0x3, 0x2, 0x2, 0x2, 0x383, 0x381, 0x3, 0x2, 0x2, 0x2, 0x383, 0x382, 
    0x3, 0x2, 0x2, 0x2, 0x384, 0x387, 0x3, 0x2, 0x2, 0x2, 0x385, 0x386, 
    0x3, 0x2, 0x2, 0x2, 0x385, 0x383, 0x3, 0x2, 0x2, 0x2, 0x386, 0x388, 
    0x3, 0x2, 0x2, 0x2, 0x387, 0x385, 0x3, 0x2, 0x2, 0x2, 0x388, 0x38c, 
    0x7, 0x50, 0x2, 0x2, 0x389, 0x38b, 0x7, 0x49, 0x2, 0x2, 0x38a, 0x389, 
    0x3, 0x2, 0x2, 0x2, 0x38b, 0x38e, 0x3, 0x2, 0x2, 0x2, 0x38c, 0x38a, 
    0x3, 0x2, 0x2, 0x2, 0x38c, 0x38d, 0x3, 0x2, 0x2, 0x2, 0x38d, 0x38f, 
    0x3, 0x2, 0x2, 0x2, 0x38e, 0x38c, 0x3, 0x2, 0x2, 0x2, 0x38f, 0x390, 
    0x9, 0x6, 0x2, 0x2, 0x390, 0xb5, 0x3, 0x2, 0x2, 0x2, 0x391, 0x3af, 0x5, 
    0xc, 0x7, 0x2, 0x392, 0x3af, 0x7, 0x45, 0x2, 0x2, 0x393, 0x3af, 0x7, 
    0x46, 0x2, 0x2, 0x394, 0x3af, 0x5, 0xc6, 0x64, 0x2, 0x395, 0x3af, 0x7, 
    0x48, 0x2, 0x2, 0x396, 0x3af, 0x5, 0x12, 0xa, 0x2, 0x397, 0x3af, 0x7, 
    0x4f, 0x2, 0x2, 0x398, 0x3af, 0x5, 0x14, 0xb, 0x2, 0x399, 0x3af, 0x5, 
    0x16, 0xc, 0x2, 0x39a, 0x3af, 0x7, 0x50, 0x2, 0x2, 0x39b, 0x3af, 0x7, 
    0x55, 0x2, 0x2, 0x39c, 0x3af, 0x7, 0x56, 0x2, 0x2, 0x39d, 0x3af, 0x7, 
    0x57, 0x2, 0x2, 0x39e, 0x3af, 0x7, 0x58, 0x2, 0x2, 0x39f, 0x3af, 0x7, 
    0x59, 0x2, 0x2, 0x3a0, 0x3af, 0x7, 0x5, 0x2, 0x2, 0x3a1, 0x3af, 0x5, 
    0xae, 0x58, 0x2, 0x3a2, 0x3af, 0x7, 0x49, 0x2, 0x2, 0x3a3, 0x3af, 0x7, 
    0x4e, 0x2, 0x2, 0x3a4, 0x3af, 0x7, 0x47, 0x2, 0x2, 0x3a5, 0x3af, 0x5, 
    0x10, 0x9, 0x2, 0x3a6, 0x3af, 0x7, 0x52, 0x2, 0x2, 0x3a7, 0x3af, 0x7, 
    0x53, 0x2, 0x2, 0x3a8, 0x3af, 0x7, 0x54, 0x2, 0x2, 0x3a9, 0x3af, 0x7, 
    0x5f, 0x2, 0x2, 0x3aa, 0x3af, 0x7, 0x5b, 0x2, 0x2, 0x3ab, 0x3af, 0x7, 
    0x5c, 0x2, 0x2, 0x3ac, 0x3af, 0x7, 0x5d, 0x2, 0x2, 0x3ad, 0x3af, 0x7, 
    0x5e, 0x2, 0x2, 0x3ae, 0x391, 0x3, 0x2, 0x2, 0x2, 0x3ae, 0x392, 0x3, 
    0x2, 0x2, 0x2, 0x3ae, 0x393, 0x3, 0x2, 0x2, 0x2, 0x3ae, 0x394, 0x3, 
    0x2, 0x2, 0x2, 0x3ae, 0x395, 0x3, 0x2, 0x2, 0x2, 0x3ae, 0x396, 0x3, 
    0x2, 0x2, 0x2, 0x3ae, 0x397, 0x3, 0x2, 0x2, 0x2, 0x3ae, 0x398, 0x3, 
    0x2, 0x2, 0x2, 0x3ae, 0x399, 0x3, 0x2, 0x2, 0x2, 0x3ae, 0x39a, 0x3, 
    0x2, 0x2, 0x2, 0x3ae, 0x39b, 0x3, 0x2, 0x2, 0x2, 0x3ae, 0x39c, 0x3, 
    0x2, 0x2, 0x2, 0x3ae, 0x39d, 0x3, 0x2, 0x2, 0x2, 0x3ae, 0x39e, 0x3, 
    0x2, 0x2, 0x2, 0x3ae, 0x39f, 0x3, 0x2, 0x2, 0x2, 0x3ae, 0x3a0, 0x3, 
    0x2, 0x2, 0x2, 0x3ae, 0x3a1, 0x3, 0x2, 0x2, 0x2, 0x3ae, 0x3a2, 0x3, 
    0x2, 0x2, 0x2, 0x3ae, 0x3a3, 0x3, 0x2, 0x2, 0x2, 0x3ae, 0x3a4, 0x3, 
    0x2, 0x2, 0x2, 0x3ae, 0x3a5, 0x3, 0x2, 0x2, 0x2, 0x3ae, 0x3a6, 0x3, 
    0x2, 0x2, 0x2, 0x3ae, 0x3a7, 0x3, 0x2, 0x2, 0x2, 0x3ae, 0x3a8, 0x3, 
    0x2, 0x2, 0x2, 0x3ae, 0x3a9, 0x3, 0x2, 0x2, 0x2, 0x3ae, 0x3aa, 0x3, 
    0x2, 0x2, 0x2, 0x3ae, 0x3ab, 0x3, 0x2, 0x2, 0x2, 0x3ae, 0x3ac, 0x3, 
    0x2, 0x2, 0x2, 0x3ae, 0x3ad, 0x3, 0x2, 0x2, 0x2, 0x3af, 0x3b2, 0x3, 
    0x2, 0x2, 0x2, 0x3b0, 0x3b1, 0x3, 0x2, 0x2, 0x2, 0x3b0, 0x3ae, 0x3, 
    0x2, 0x2, 0x2, 0x3b1, 0x3bb, 0x3, 0x2, 0x2, 0x2, 0x3b2, 0x3b0, 0x3, 
    0x2, 0x2, 0x2, 0x3b3, 0x3b7, 0x7, 0x51, 0x2, 0x2, 0x3b4, 0x3b6, 0x7, 
    0x49, 0x2, 0x2, 0x3b5, 0x3b4, 0x3, 0x2, 0x2, 0x2, 0x3b6, 0x3b9, 0x3, 
    0x2, 0x2, 0x2, 0x3b7, 0x3b5, 0x3, 0x2, 0x2, 0x2, 0x3b7, 0x3b8, 0x3, 
    0x2, 0x2, 0x2, 0x3b8, 0x3bc, 0x3, 0x2, 0x2, 0x2, 0x3b9, 0x3b7, 0x3, 
    0x2, 0x2, 0x2, 0x3ba, 0x3bc, 0x7, 0x2, 0x2, 0x3, 0x3bb, 0x3b3, 0x3, 
    0x2, 0x2, 0x2, 0x3bb, 0x3ba, 0x3, 0x2, 0x2, 0x2, 0x3bc, 0xb7, 0x3, 0x2, 
    0x2, 0x2, 0x3bd, 0x3db, 0x5, 0xc, 0x7, 0x2, 0x3be, 0x3db, 0x7, 0x45, 
    0x2, 0x2, 0x3bf, 0x3db, 0x7, 0x46, 0x2, 0x2, 0x3c0, 0x3db, 0x5, 0xc6, 
    0x64, 0x2, 0x3c1, 0x3db, 0x7, 0x48, 0x2, 0x2, 0x3c2, 0x3db, 0x5, 0x12, 
    0xa, 0x2, 0x3c3, 0x3db, 0x5, 0x14, 0xb, 0x2, 0x3c4, 0x3db, 0x5, 0x16, 
    0xc, 0x2, 0x3c5, 0x3db, 0x7, 0x4f, 0x2, 0x2, 0x3c6, 0x3db, 0x7, 0x55, 
    0x2, 0x2, 0x3c7, 0x3db, 0x7, 0x56, 0x2, 0x2, 0x3c8, 0x3db, 0x7, 0x57, 
    0x2, 0x2, 0x3c9, 0x3db, 0x7, 0x58, 0x2, 0x2, 0x3ca, 0x3db, 0x7, 0x59, 
    0x2, 0x2, 0x3cb, 0x3db, 0x7, 0x5, 0x2, 0x2, 0x3cc, 0x3db, 0x7, 0x49, 
    0x2, 0x2, 0x3cd, 0x3db, 0x7, 0x4e, 0x2, 0x2, 0x3ce, 0x3db, 0x7, 0x47, 
    0x2, 0x2, 0x3cf, 0x3db, 0x5, 0x10, 0x9, 0x2, 0x3d0, 0x3db, 0x7, 0x52, 
    0x2, 0x2, 0x3d1, 0x3db, 0x7, 0x53, 0x2, 0x2, 0x3d2, 0x3db, 0x7, 0x54, 
    0x2, 0x2, 0x3d3, 0x3db, 0x7, 0x5f, 0x2, 0x2, 0x3d4, 0x3db, 0x7, 0x5b, 
    0x2, 0x2, 0x3d5, 0x3db, 0x7, 0x5c, 0x2, 0x2, 0x3d6, 0x3db, 0x7, 0x5d, 
    0x2, 0x2, 0x3d7, 0x3db, 0x7, 0x5e, 0x2, 0x2, 0x3d8, 0x3db, 0x7, 0x11, 
    0x2, 0x2, 0x3d9, 0x3db, 0x5, 0xae, 0x58, 0x2, 0x3da, 0x3bd, 0x3, 0x2, 
    0x2, 0x2, 0x3da, 0x3be, 0x3, 0x2, 0x2, 0x2, 0x3da, 0x3bf, 0x3, 0x2, 
    0x2, 0x2, 0x3da, 0x3c0, 0x3, 0x2, 0x2, 0x2, 0x3da, 0x3c1, 0x3, 0x2, 
    0x2, 0x2, 0x3da, 0x3c2, 0x3, 0x2, 0x2, 0x2, 0x3da, 0x3c3, 0x3, 0x2, 
    0x2, 0x2, 0x3da, 0x3c4, 0x3, 0x2, 0x2, 0x2, 0x3da, 0x3c5, 0x3, 0x2, 
    0x2, 0x2, 0x3da, 0x3c6, 0x3, 0x2, 0x2, 0x2, 0x3da, 0x3c7, 0x3, 0x2, 
    0x2, 0x2, 0x3da, 0x3c8, 0x3, 0x2, 0x2, 0x2, 0x3da, 0x3c9, 0x3, 0x2, 
    0x2, 0x2, 0x3da, 0x3ca, 0x3, 0x2, 0x2, 0x2, 0x3da, 0x3cb, 0x3, 0x2, 
    0x2, 0x2, 0x3da, 0x3cc, 0x3, 0x2, 0x2, 0x2, 0x3da, 0x3cd, 0x3, 0x2, 
    0x2, 0x2, 0x3da, 0x3ce, 0x3, 0x2, 0x2, 0x2, 0x3da, 0x3cf, 0x3, 0x2, 
    0x2, 0x2, 0x3da, 0x3d0, 0x3, 0x2, 0x2, 0x2, 0x3da, 0x3d1, 0x3, 0x2, 
    0x2, 0x2, 0x3da, 0x3d2, 0x3, 0x2, 0x2, 0x2, 0x3da, 0x3d3, 0x3, 0x2, 
    0x2, 0x2, 0x3da, 0x3d4, 0x3, 0x2, 0x2, 0x2, 0x3da, 0x3d5, 0x3, 0x2, 
    0x2, 0x2, 0x3da, 0x3d6, 0x3, 0x2, 0x2, 0x2, 0x3da, 0x3d7, 0x3, 0x2, 
    0x2, 0x2, 0x3da, 0x3d8, 0x3, 0x2, 0x2, 0x2, 0x3da, 0x3d9, 0x3, 0x2, 
    0x2, 0x2, 0x3db, 0x3de, 0x3, 0x2, 0x2, 0x2, 0x3dc, 0x3dd, 0x3, 0x2, 
    0x2, 0x2, 0x3dc, 0x3da, 0x3, 0x2, 0x2, 0x2, 0x3dd, 0xb9, 0x3, 0x2, 0x2, 
    0x2, 0x3de, 0x3dc, 0x3, 0x2, 0x2, 0x2, 0x3df, 0x3fb, 0x5, 0xc, 0x7, 
    0x2, 0x3e0, 0x3fb, 0x7, 0x45, 0x2, 0x2, 0x3e1, 0x3fb, 0x7, 0x46, 0x2, 
    0x2, 0x3e2, 0x3fb, 0x5, 0xc6, 0x64, 0x2, 0x3e3, 0x3fb, 0x7, 0x48, 0x2, 
    0x2, 0x3e4, 0x3fb, 0x5, 0x12, 0xa, 0x2, 0x3e5, 0x3fb, 0x5, 0x14, 0xb, 
    0x2, 0x3e6, 0x3fb, 0x5, 0x16, 0xc, 0x2, 0x3e7, 0x3fb, 0x7, 0x4f, 0x2, 
    0x2, 0x3e8, 0x3fb, 0x7, 0x55, 0x2, 0x2, 0x3e9, 0x3fb, 0x7, 0x56, 0x2, 
    0x2, 0x3ea, 0x3fb, 0x7, 0x57, 0x2, 0x2, 0x3eb, 0x3fb, 0x7, 0x58, 0x2, 
    0x2, 0x3ec, 0x3fb, 0x7, 0x59, 0x2, 0x2, 0x3ed, 0x3fb, 0x7, 0x5, 0x2, 
    0x2, 0x3ee, 0x3fb, 0x7, 0x49, 0x2, 0x2, 0x3ef, 0x3fb, 0x7, 0x4e, 0x2, 
    0x2, 0x3f0, 0x3fb, 0x7, 0x47, 0x2, 0x2, 0x3f1, 0x3fb, 0x5, 0x10, 0x9, 
    0x2, 0x3f2, 0x3fb, 0x7, 0x52, 0x2, 0x2, 0x3f3, 0x3fb, 0x7, 0x53, 0x2, 
    0x2, 0x3f4, 0x3fb, 0x7, 0x54, 0x2, 0x2, 0x3f5, 0x3fb, 0x7, 0x5f, 0x2, 
    0x2, 0x3f6, 0x3fb, 0x7, 0x5b, 0x2, 0x2, 0x3f7, 0x3fb, 0x7, 0x5c, 0x2, 
    0x2, 0x3f8, 0x3fb, 0x7, 0x5d, 0x2, 0x2, 0x3f9, 0x3fb, 0x7, 0x5e, 0x2, 
    0x2, 0x3fa, 0x3df, 0x3, 0x2, 0x2, 0x2, 0x3fa, 0x3e0, 0x3, 0x2, 0x2, 
    0x2, 0x3fa, 0x3e1, 0x3, 0x2, 0x2, 0x2, 0x3fa, 0x3e2, 0x3, 0x2, 0x2, 
    0x2, 0x3fa, 0x3e3, 0x3, 0x2, 0x2, 0x2, 0x3fa, 0x3e4, 0x3, 0x2, 0x2, 
    0x2, 0x3fa, 0x3e5, 0x3, 0x2, 0x2, 0x2, 0x3fa, 0x3e6, 0x3, 0x2, 0x2, 
    0x2, 0x3fa, 0x3e7, 0x3, 0x2, 0x2, 0x2, 0x3fa, 0x3e8, 0x3, 0x2, 0x2, 
    0x2, 0x3fa, 0x3e9, 0x3, 0x2, 0x2, 0x2, 0x3fa, 0x3ea, 0x3, 0x2, 0x2, 
    0x2, 0x3fa, 0x3eb, 0x3, 0x2, 0x2, 0x2, 0x3fa, 0x3ec, 0x3, 0x2, 0x2, 
    0x2, 0x3fa, 0x3ed, 0x3, 0x2, 0x2, 0x2, 0x3fa, 0x3ee, 0x3, 0x2, 0x2, 
    0x2, 0x3fa, 0x3ef, 0x3, 0x2, 0x2, 0x2, 0x3fa, 0x3f0, 0x3, 0x2, 0x2, 
    0x2, 0x3fa, 0x3f1, 0x3, 0x2, 0x2, 0x2, 0x3fa, 0x3f2, 0x3, 0x2, 0x2, 
    0x2, 0x3fa, 0x3f3, 0x3, 0x2, 0x2, 0x2, 0x3fa, 0x3f4, 0x3, 0x2, 0x2, 
    0x2, 0x3fa, 0x3f5, 0x3, 0x2, 0x2, 0x2, 0x3fa, 0x3f6, 0x3, 0x2, 0x2, 
    0x2, 0x3fa, 0x3f7, 0x3, 0x2, 0x2, 0x2, 0x3fa, 0x3f8, 0x3, 0x2, 0x2, 
    0x2, 0x3fa, 0x3f9, 0x3, 0x2, 0x2, 0x2, 0x3fb, 0x3fe, 0x3, 0x2, 0x2, 
    0x2, 0x3fc, 0x3fd, 0x3, 0x2, 0x2, 0x2, 0x3fc, 0x3fa, 0x3, 0x2, 0x2, 
    0x2, 0x3fd, 0xbb, 0x3, 0x2, 0x2, 0x2, 0x3fe, 0x3fc, 0x3, 0x2, 0x2, 0x2, 
    0x3ff, 0x413, 0x7, 0x48, 0x2, 0x2, 0x400, 0x413, 0x5, 0x12, 0xa, 0x2, 
    0x401, 0x413, 0x7, 0x49, 0x2, 0x2, 0x402, 0x413, 0x7, 0x4e, 0x2, 0x2, 
    0x403, 0x413, 0x7, 0x47, 0x2, 0x2, 0x404, 0x413, 0x7, 0x5b, 0x2, 0x2, 
    0x405, 0x413, 0x7, 0x5c, 0x2, 0x2, 0x406, 0x413, 0x7, 0x5d, 0x2, 0x2, 
    0x407, 0x413, 0x7, 0x5e, 0x2, 0x2, 0x408, 0x413, 0x7, 0x55, 0x2, 0x2, 
    0x409, 0x413, 0x7, 0x56, 0x2, 0x2, 0x40a, 0x413, 0x7, 0x57, 0x2, 0x2, 
    0x40b, 0x413, 0x7, 0x58, 0x2, 0x2, 0x40c, 0x413, 0x7, 0x59, 0x2, 0x2, 
    0x40d, 0x413, 0x5, 0xc6, 0x64, 0x2, 0x40e, 0x413, 0x5, 0x14, 0xb, 0x2, 
    0x40f, 0x413, 0x5, 0x16, 0xc, 0x2, 0x410, 0x413, 0x7, 0x5f, 0x2, 0x2, 
    0x411, 0x413, 0x7, 0x60, 0x2, 0x2, 0x412, 0x3ff, 0x3, 0x2, 0x2, 0x2, 
    0x412, 0x400, 0x3, 0x2, 0x2, 0x2, 0x412, 0x401, 0x3, 0x2, 0x2, 0x2, 
    0x412, 0x402, 0x3, 0x2, 0x2, 0x2, 0x412, 0x403, 0x3, 0x2, 0x2, 0x2, 
    0x412, 0x404, 0x3, 0x2, 0x2, 0x2, 0x412, 0x405, 0x3, 0x2, 0x2, 0x2, 
    0x412, 0x406, 0x3, 0x2, 0x2, 0x2, 0x412, 0x407, 0x3, 0x2, 0x2, 0x2, 
    0x412, 0x408, 0x3, 0x2, 0x2, 0x2, 0x412, 0x409, 0x3, 0x2, 0x2, 0x2, 
    0x412, 0x40a, 0x3, 0x2, 0x2, 0x2, 0x412, 0x40b, 0x3, 0x2, 0x2, 0x2, 
    0x412, 0x40c, 0x3, 0x2, 0x2, 0x2, 0x412, 0x40d, 0x3, 0x2, 0x2, 0x2, 
    0x412, 0x40e, 0x3, 0x2, 0x2, 0x2, 0x412, 0x40f, 0x3, 0x2, 0x2, 0x2, 
    0x412, 0x410, 0x3, 0x2, 0x2, 0x2, 0x412, 0x411, 0x3, 0x2, 0x2, 0x2, 
    0x413, 0xbd, 0x3, 0x2, 0x2, 0x2, 0x414, 0x428, 0x7, 0x48, 0x2, 0x2, 
    0x415, 0x428, 0x5, 0x12, 0xa, 0x2, 0x416, 0x428, 0x7, 0x49, 0x2, 0x2, 
    0x417, 0x428, 0x7, 0x4e, 0x2, 0x2, 0x418, 0x428, 0x7, 0x47, 0x2, 0x2, 
    0x419, 0x428, 0x5, 0xc0, 0x61, 0x2, 0x41a, 0x428, 0x7, 0x58, 0x2, 0x2, 
    0x41b, 0x428, 0x7, 0x59, 0x2, 0x2, 0x41c, 0x428, 0x5, 0xa, 0x6, 0x2, 
    0x41d, 0x428, 0x7, 0x51, 0x2, 0x2, 0x41e, 0x428, 0x7, 0x4f, 0x2, 0x2, 
    0x41f, 0x428, 0x5, 0xc6, 0x64, 0x2, 0x420, 0x428, 0x5, 0xac, 0x57, 0x2, 
    0x421, 0x428, 0x5, 0xaa, 0x56, 0x2, 0x422, 0x428, 0x5, 0x10, 0x9, 0x2, 
    0x423, 0x428, 0x5, 0x14, 0xb, 0x2, 0x424, 0x428, 0x5, 0x16, 0xc, 0x2, 
    0x425, 0x428, 0x7, 0x5f, 0x2, 0x2, 0x426, 0x428, 0x7, 0x60, 0x2, 0x2, 
    0x427, 0x414, 0x3, 0x2, 0x2, 0x2, 0x427, 0x415, 0x3, 0x2, 0x2, 0x2, 
    0x427, 0x416, 0x3, 0x2, 0x2, 0x2, 0x427, 0x417, 0x3, 0x2, 0x2, 0x2, 
    0x427, 0x418, 0x3, 0x2, 0x2, 0x2, 0x427, 0x419, 0x3, 0x2, 0x2, 0x2, 
    0x427, 0x41a, 0x3, 0x2, 0x2, 0x2, 0x427, 0x41b, 0x3, 0x2, 0x2, 0x2, 
    0x427, 0x41c, 0x3, 0x2, 0x2, 0x2, 0x427, 0x41d, 0x3, 0x2, 0x2, 0x2, 
    0x427, 0x41e, 0x3, 0x2, 0x2, 0x2, 0x427, 0x41f, 0x3, 0x2, 0x2, 0x2, 
    0x427, 0x420, 0x3, 0x2, 0x2, 0x2, 0x427, 0x421, 0x3, 0x2, 0x2, 0x2, 
    0x427, 0x422, 0x3, 0x2, 0x2, 0x2, 0x427, 0x423, 0x3, 0x2, 0x2, 0x2, 
    0x427, 0x424, 0x3, 0x2, 0x2, 0x2, 0x427, 0x425, 0x3, 0x2, 0x2, 0x2, 
    0x427, 0x426, 0x3, 0x2, 0x2, 0x2, 0x428, 0xbf, 0x3, 0x2, 0x2, 0x2, 0x429, 
    0x43c, 0x7, 0x55, 0x2, 0x2, 0x42a, 0x43b, 0x7, 0x48, 0x2, 0x2, 0x42b, 
    0x43b, 0x5, 0x12, 0xa, 0x2, 0x42c, 0x43b, 0x7, 0x49, 0x2, 0x2, 0x42d, 
    0x43b, 0x7, 0x4e, 0x2, 0x2, 0x42e, 0x43b, 0x7, 0x47, 0x2, 0x2, 0x42f, 
    0x43b, 0x7, 0x57, 0x2, 0x2, 0x430, 0x43b, 0x7, 0x58, 0x2, 0x2, 0x431, 
    0x43b, 0x7, 0x59, 0x2, 0x2, 0x432, 0x43b, 0x5, 0xa, 0x6, 0x2, 0x433, 
    0x43b, 0x7, 0x4f, 0x2, 0x2, 0x434, 0x43b, 0x7, 0x51, 0x2, 0x2, 0x435, 
    0x43b, 0x5, 0xc0, 0x61, 0x2, 0x436, 0x43b, 0x5, 0xc6, 0x64, 0x2, 0x437, 
    0x43b, 0x5, 0x10, 0x9, 0x2, 0x438, 0x43b, 0x7, 0x5f, 0x2, 0x2, 0x439, 
    0x43b, 0x7, 0x60, 0x2, 0x2, 0x43a, 0x42a, 0x3, 0x2, 0x2, 0x2, 0x43a, 
    0x42b, 0x3, 0x2, 0x2, 0x2, 0x43a, 0x42c, 0x3, 0x2, 0x2, 0x2, 0x43a, 
    0x42d, 0x3, 0x2, 0x2, 0x2, 0x43a, 0x42e, 0x3, 0x2, 0x2, 0x2, 0x43a, 
    0x42f, 0x3, 0x2, 0x2, 0x2, 0x43a, 0x430, 0x3, 0x2, 0x2, 0x2, 0x43a, 
    0x431, 0x3, 0x2, 0x2, 0x2, 0x43a, 0x432, 0x3, 0x2, 0x2, 0x2, 0x43a, 
    0x433, 0x3, 0x2, 0x2, 0x2, 0x43a, 0x434, 0x3, 0x2, 0x2, 0x2, 0x43a, 
    0x435, 0x3, 0x2, 0x2, 0x2, 0x43a, 0x436, 0x3, 0x2, 0x2, 0x2, 0x43a, 
    0x437, 0x3, 0x2, 0x2, 0x2, 0x43a, 0x438, 0x3, 0x2, 0x2, 0x2, 0x43a, 
    0x439, 0x3, 0x2, 0x2, 0x2, 0x43b, 0x43e, 0x3, 0x2, 0x2, 0x2, 0x43c, 
    0x43a, 0x3, 0x2, 0x2, 0x2, 0x43c, 0x43d, 0x3, 0x2, 0x2, 0x2, 0x43d, 
    0x43f, 0x3, 0x2, 0x2, 0x2, 0x43e, 0x43c, 0x3, 0x2, 0x2, 0x2, 0x43f, 
    0x46d, 0x7, 0x56, 0x2, 0x2, 0x440, 0x452, 0x7, 0x5b, 0x2, 0x2, 0x441, 
    0x451, 0x7, 0x48, 0x2, 0x2, 0x442, 0x451, 0x5, 0x12, 0xa, 0x2, 0x443, 
    0x451, 0x7, 0x49, 0x2, 0x2, 0x444, 0x451, 0x7, 0x4e, 0x2, 0x2, 0x445, 
    0x451, 0x7, 0x47, 0x2, 0x2, 0x446, 0x451, 0x7, 0x57, 0x2, 0x2, 0x447, 
    0x451, 0x7, 0x58, 0x2, 0x2, 0x448, 0x451, 0x7, 0x59, 0x2, 0x2, 0x449, 
    0x451, 0x5, 0xa, 0x6, 0x2, 0x44a, 0x451, 0x7, 0x51, 0x2, 0x2, 0x44b, 
    0x451, 0x5, 0xc0, 0x61, 0x2, 0x44c, 0x451, 0x5, 0xc6, 0x64, 0x2, 0x44d, 
    0x451, 0x5, 0x10, 0x9, 0x2, 0x44e, 0x451, 0x7, 0x5f, 0x2, 0x2, 0x44f, 
    0x451, 0x7, 0x60, 0x2, 0x2, 0x450, 0x441, 0x3, 0x2, 0x2, 0x2, 0x450, 
    0x442, 0x3, 0x2, 0x2, 0x2, 0x450, 0x443, 0x3, 0x2, 0x2, 0x2, 0x450, 
    0x444, 0x3, 0x2, 0x2, 0x2, 0x450, 0x445, 0x3, 0x2, 0x2, 0x2, 0x450, 
    0x446, 0x3, 0x2, 0x2, 0x2, 0x450, 0x447, 0x3, 0x2, 0x2, 0x2, 0x450, 
    0x448, 0x3, 0x2, 0x2, 0x2, 0x450, 0x449, 0x3, 0x2, 0x2, 0x2, 0x450, 
    0x44a, 0x3, 0x2, 0x2, 0x2, 0x450, 0x44b, 0x3, 0x2, 0x2, 0x2, 0x450, 
    0x44c, 0x3, 0x2, 0x2, 0x2, 0x450, 0x44d, 0x3, 0x2, 0x2, 0x2, 0x450, 
    0x44e, 0x3, 0x2, 0x2, 0x2, 0x450, 0x44f, 0x3, 0x2, 0x2, 0x2, 0x451, 
    0x454, 0x3, 0x2, 0x2, 0x2, 0x452, 0x450, 0x3, 0x2, 0x2, 0x2, 0x452, 
    0x453, 0x3, 0x2, 0x2, 0x2, 0x453, 0x455, 0x3, 0x2, 0x2, 0x2, 0x454, 
    0x452, 0x3, 0x2, 0x2, 0x2, 0x455, 0x46d, 0x7, 0x5c, 0x2, 0x2, 0x456, 
    0x468, 0x7, 0x5d, 0x2, 0x2, 0x457, 0x467, 0x7, 0x48, 0x2, 0x2, 0x458, 
    0x467, 0x5, 0x12, 0xa, 0x2, 0x459, 0x467, 0x7, 0x49, 0x2, 0x2, 0x45a, 
    0x467, 0x7, 0x4e, 0x2, 0x2, 0x45b, 0x467, 0x7, 0x47, 0x2, 0x2, 0x45c, 
    0x467, 0x7, 0x57, 0x2, 0x2, 0x45d, 0x467, 0x7, 0x58, 0x2, 0x2, 0x45e, 
    0x467, 0x7, 0x59, 0x2, 0x2, 0x45f, 0x467, 0x5, 0xa, 0x6, 0x2, 0x460, 
    0x467, 0x7, 0x51, 0x2, 0x2, 0x461, 0x467, 0x5, 0xc0, 0x61, 0x2, 0x462, 
    0x467, 0x5, 0xc6, 0x64, 0x2, 0x463, 0x467, 0x5, 0x10, 0x9, 0x2, 0x464, 
    0x467, 0x7, 0x5f, 0x2, 0x2, 0x465, 0x467, 0x7, 0x60, 0x2, 0x2, 0x466, 
    0x457, 0x3, 0x2, 0x2, 0x2, 0x466, 0x458, 0x3, 0x2, 0x2, 0x2, 0x466, 
    0x459, 0x3, 0x2, 0x2, 0x2, 0x466, 0x45a, 0x3, 0x2, 0x2, 0x2, 0x466, 
    0x45b, 0x3, 0x2, 0x2, 0x2, 0x466, 0x45c, 0x3, 0x2, 0x2, 0x2, 0x466, 
    0x45d, 0x3, 0x2, 0x2, 0x2, 0x466, 0x45e, 0x3, 0x2, 0x2, 0x2, 0x466, 
    0x45f, 0x3, 0x2, 0x2, 0x2, 0x466, 0x460, 0x3, 0x2, 0x2, 0x2, 0x466, 
    0x461, 0x3, 0x2, 0x2, 0x2, 0x466, 0x462, 0x3, 0x2, 0x2, 0x2, 0x466, 
    0x463, 0x3, 0x2, 0x2, 0x2, 0x466, 0x464, 0x3, 0x2, 0x2, 0x2, 0x466, 
    0x465, 0x3, 0x2, 0x2, 0x2, 0x467, 0x46a, 0x3, 0x2, 0x2, 0x2, 0x468, 
    0x466, 0x3, 0x2, 0x2, 0x2, 0x468, 0x469, 0x3, 0x2, 0x2, 0x2, 0x469, 
    0x46b, 0x3, 0x2, 0x2, 0x2, 0x46a, 0x468, 0x3, 0x2, 0x2, 0x2, 0x46b, 
    0x46d, 0x7, 0x5e, 0x2, 0x2, 0x46c, 0x429, 0x3, 0x2, 0x2, 0x2, 0x46c, 
    0x440, 0x3, 0x2, 0x2, 0x2, 0x46c, 0x456, 0x3, 0x2, 0x2, 0x2, 0x46d, 
    0xc1, 0x3, 0x2, 0x2, 0x2, 0x46e, 0x489, 0x7, 0x48, 0x2, 0x2, 0x46f, 
    0x489, 0x5, 0x12, 0xa, 0x2, 0x470, 0x489, 0x7, 0x51, 0x2, 0x2, 0x471, 
    0x489, 0x7, 0x49, 0x2, 0x2, 0x472, 0x489, 0x7, 0x4e, 0x2, 0x2, 0x473, 
    0x489, 0x7, 0x50, 0x2, 0x2, 0x474, 0x489, 0x7, 0x47, 0x2, 0x2, 0x475, 
    0x489, 0x7, 0x55, 0x2, 0x2, 0x476, 0x489, 0x7, 0x56, 0x2, 0x2, 0x477, 
    0x489, 0x7, 0x57, 0x2, 0x2, 0x478, 0x489, 0x7, 0x58, 0x2, 0x2, 0x479, 
    0x489, 0x7, 0x59, 0x2, 0x2, 0x47a, 0x489, 0x7, 0x5b, 0x2, 0x2, 0x47b, 
    0x489, 0x7, 0x5c, 0x2, 0x2, 0x47c, 0x489, 0x7, 0x5d, 0x2, 0x2, 0x47d, 
    0x489, 0x7, 0x5e, 0x2, 0x2, 0x47e, 0x489, 0x7, 0x54, 0x2, 0x2, 0x47f, 
    0x489, 0x7, 0x5, 0x2, 0x2, 0x480, 0x489, 0x7, 0x4c, 0x2, 0x2, 0x481, 
    0x489, 0x5, 0x14, 0xb, 0x2, 0x482, 0x489, 0x5, 0x16, 0xc, 0x2, 0x483, 
    0x489, 0x7, 0x52, 0x2, 0x2, 0x484, 0x489, 0x7, 0x53, 0x2, 0x2, 0x485, 
    0x489, 0x7, 0x4f, 0x2, 0x2, 0x486, 0x489, 0x7, 0x5f, 0x2, 0x2, 0x487, 
    0x489, 0x7, 0x60, 0x2, 0x2, 0x488, 0x46e, 0x3, 0x2, 0x2, 0x2, 0x488, 
    0x46f, 0x3, 0x2, 0x2, 0x2, 0x488, 0x470, 0x3, 0x2, 0x2, 0x2, 0x488, 
    0x471, 0x3, 0x2, 0x2, 0x2, 0x488, 0x472, 0x3, 0x2, 0x2, 0x2, 0x488, 
    0x473, 0x3, 0x2, 0x2, 0x2, 0x488, 0x474, 0x3, 0x2, 0x2, 0x2, 0x488, 
    0x475, 0x3, 0x2, 0x2, 0x2, 0x488, 0x476, 0x3, 0x2, 0x2, 0x2, 0x488, 
    0x477, 0x3, 0x2, 0x2, 0x2, 0x488, 0x478, 0x3, 0x2, 0x2, 0x2, 0x488, 
    0x479, 0x3, 0x2, 0x2, 0x2, 0x488, 0x47a, 0x3, 0x2, 0x2, 0x2, 0x488, 
    0x47b, 0x3, 0x2, 0x2, 0x2, 0x488, 0x47c, 0x3, 0x2, 0x2, 0x2, 0x488, 
    0x47d, 0x3, 0x2, 0x2, 0x2, 0x488, 0x47e, 0x3, 0x2, 0x2, 0x2, 0x488, 
    0x47f, 0x3, 0x2, 0x2, 0x2, 0x488, 0x480, 0x3, 0x2, 0x2, 0x2, 0x488, 
    0x481, 0x3, 0x2, 0x2, 0x2, 0x488, 0x482, 0x3, 0x2, 0x2, 0x2, 0x488, 
    0x483, 0x3, 0x2, 0x2, 0x2, 0x488, 0x484, 0x3, 0x2, 0x2, 0x2, 0x488, 
    0x485, 0x3, 0x2, 0x2, 0x2, 0x488, 0x486, 0x3, 0x2, 0x2, 0x2, 0x488, 
    0x487, 0x3, 0x2, 0x2, 0x2, 0x489, 0xc3, 0x3, 0x2, 0x2, 0x2, 0x48a, 0x48b, 
    0x7, 0x47, 0x2, 0x2, 0x48b, 0xc5, 0x3, 0x2, 0x2, 0x2, 0x48c, 0x48d, 
    0x7, 0x5a, 0x2, 0x2, 0x48d, 0xc7, 0x3, 0x2, 0x2, 0x2, 0x48e, 0x49d, 
    0x7, 0x48, 0x2, 0x2, 0x48f, 0x49d, 0x5, 0x12, 0xa, 0x2, 0x490, 0x49d, 
    0x7, 0x49, 0x2, 0x2, 0x491, 0x49d, 0x7, 0x4e, 0x2, 0x2, 0x492, 0x49d, 
    0x7, 0x47, 0x2, 0x2, 0x493, 0x49d, 0x7, 0x5b, 0x2, 0x2, 0x494, 0x49d, 
    0x7, 0x5c, 0x2, 0x2, 0x495, 0x49d, 0x7, 0x5d, 0x2, 0x2, 0x496, 0x49d, 
    0x7, 0x5e, 0x2, 0x2, 0x497, 0x49d, 0x5, 0xc0, 0x61, 0x2, 0x498, 0x49d, 
    0x5, 0xc6, 0x64, 0x2, 0x499, 0x49d, 0x5, 0xa, 0x6, 0x2, 0x49a, 0x49d, 
    0x7, 0x5f, 0x2, 0x2, 0x49b, 0x49d, 0x7, 0x60, 0x2, 0x2, 0x49c, 0x48e, 
    0x3, 0x2, 0x2, 0x2, 0x49c, 0x48f, 0x3, 0x2, 0x2, 0x2, 0x49c, 0x490, 
    0x3, 0x2, 0x2, 0x2, 0x49c, 0x491, 0x3, 0x2, 0x2, 0x2, 0x49c, 0x492, 
    0x3, 0x2, 0x2, 0x2, 0x49c, 0x493, 0x3, 0x2, 0x2, 0x2, 0x49c, 0x494, 
    0x3, 0x2, 0x2, 0x2, 0x49c, 0x495, 0x3, 0x2, 0x2, 0x2, 0x49c, 0x496, 
    0x3, 0x2, 0x2, 0x2, 0x49c, 0x497, 0x3, 0x2, 0x2, 0x2, 0x49c, 0x498, 
    0x3, 0x2, 0x2, 0x2, 0x49c, 0x499, 0x3, 0x2, 0x2, 0x2, 0x49c, 0x49a, 
    0x3, 0x2, 0x2, 0x2, 0x49c, 0x49b, 0x3, 0x2, 0x2, 0x2, 0x49d, 0xc9, 0x3, 
    0x2, 0x2, 0x2, 0x49e, 0x4b4, 0x7, 0x48, 0x2, 0x2, 0x49f, 0x4b4, 0x5, 
    0x12, 0xa, 0x2, 0x4a0, 0x4b4, 0x7, 0x49, 0x2, 0x2, 0x4a1, 0x4b4, 0x7, 
    0x4e, 0x2, 0x2, 0x4a2, 0x4b4, 0x7, 0x50, 0x2, 0x2, 0x4a3, 0x4b4, 0x7, 
    0x55, 0x2, 0x2, 0x4a4, 0x4b4, 0x7, 0x56, 0x2, 0x2, 0x4a5, 0x4b4, 0x7, 
    0x57, 0x2, 0x2, 0x4a6, 0x4b4, 0x7, 0x58, 0x2, 0x2, 0x4a7, 0x4b4, 0x7, 
    0x59, 0x2, 0x2, 0x4a8, 0x4b4, 0x7, 0x5b, 0x2, 0x2, 0x4a9, 0x4b4, 0x7, 
    0x5c, 0x2, 0x2, 0x4aa, 0x4b4, 0x7, 0x5d, 0x2, 0x2, 0x4ab, 0x4b4, 0x7, 
    0x5e, 0x2, 0x2, 0x4ac, 0x4b4, 0x5, 0xc6, 0x64, 0x2, 0x4ad, 0x4b4, 0x7, 
    0x4c, 0x2, 0x2, 0x4ae, 0x4b4, 0x5, 0x14, 0xb, 0x2, 0x4af, 0x4b4, 0x5, 
    0x16, 0xc, 0x2, 0x4b0, 0x4b4, 0x7, 0x4f, 0x2, 0x2, 0x4b1, 0x4b4, 0x7, 
    0x5f, 0x2, 0x2, 0x4b2, 0x4b4, 0x7, 0x60, 0x2, 0x2, 0x4b3, 0x49e, 0x3, 
    0x2, 0x2, 0x2, 0x4b3, 0x49f, 0x3, 0x2, 0x2, 0x2, 0x4b3, 0x4a0, 0x3, 
    0x2, 0x2, 0x2, 0x4b3, 0x4a1, 0x3, 0x2, 0x2, 0x2, 0x4b3, 0x4a2, 0x3, 
    0x2, 0x2, 0x2, 0x4b3, 0x4a3, 0x3, 0x2, 0x2, 0x2, 0x4b3, 0x4a4, 0x3, 
    0x2, 0x2, 0x2, 0x4b3, 0x4a5, 0x3, 0x2, 0x2, 0x2, 0x4b3, 0x4a6, 0x3, 
    0x2, 0x2, 0x2, 0x4b3, 0x4a7, 0x3, 0x2, 0x2, 0x2, 0x4b3, 0x4a8, 0x3, 
    0x2, 0x2, 0x2, 0x4b3, 0x4a9, 0x3, 0x2, 0x2, 0x2, 0x4b3, 0x4aa, 0x3, 
    0x2, 0x2, 0x2, 0x4b3, 0x4ab, 0x3, 0x2, 0x2, 0x2, 0x4b3, 0x4ac, 0x3, 
    0x2, 0x2, 0x2, 0x4b3, 0x4ad, 0x3, 0x2, 0x2, 0x2, 0x4b3, 0x4ae, 0x3, 
    0x2, 0x2, 0x2, 0x4b3, 0x4af, 0x3, 0x2, 0x2, 0x2, 0x4b3, 0x4b0, 0x3, 
    0x2, 0x2, 0x2, 0x4b3, 0x4b1, 0x3, 0x2, 0x2, 0x2, 0x4b3, 0x4b2, 0x3, 
    0x2, 0x2, 0x2, 0x4b4, 0xcb, 0x3, 0x2, 0x2, 0x2, 0x53, 0xd3, 0x120, 0x126, 
    0x12e, 0x134, 0x13c, 0x143, 0x148, 0x158, 0x160, 0x179, 0x180, 0x187, 
    0x18e, 0x195, 0x19c, 0x1a3, 0x1aa, 0x1b1, 0x1b9, 0x1be, 0x1d0, 0x1d5, 
    0x1dc, 0x1e5, 0x1ee, 0x1f7, 0x20a, 0x22d, 0x237, 0x268, 0x273, 0x27f, 
    0x291, 0x295, 0x2a6, 0x2ab, 0x2af, 0x2b3, 0x2ba, 0x2c2, 0x2c7, 0x2ce, 
    0x2d2, 0x2d8, 0x2e2, 0x2e5, 0x326, 0x32d, 0x334, 0x339, 0x340, 0x347, 
    0x34e, 0x353, 0x358, 0x35d, 0x364, 0x383, 0x385, 0x38c, 0x3ae, 0x3b0, 
    0x3b7, 0x3bb, 0x3da, 0x3dc, 0x3fa, 0x3fc, 0x412, 0x427, 0x43a, 0x43c, 
    0x450, 0x452, 0x466, 0x468, 0x46c, 0x488, 0x49c, 0x4b3, 
  };

  atn::ATNDeserializer deserializer;
  _atn = deserializer.deserialize(_serializedATN);

  size_t count = _atn.getNumberOfDecisions();
  _decisionToDFA.reserve(count);
  for (size_t i = 0; i < count; i++) { 
    _decisionToDFA.emplace_back(_atn.getDecisionState(i), i);
  }
}

SV3_1aPpParser::Initializer SV3_1aPpParser::_init;
