
// Generated from SV3_1aSplitterParser.g4 by ANTLR 4.9.1


#include "SV3_1aSplitterParserListener.h"

#include "SV3_1aSplitterParser.h"


using namespace antlrcpp;
using namespace antlr4;

SV3_1aSplitterParser::SV3_1aSplitterParser(TokenStream *input) : Parser(input) {
  _interpreter = new atn::ParserATNSimulator(this, _atn, _decisionToDFA, _sharedContextCache);
}

SV3_1aSplitterParser::~SV3_1aSplitterParser() {
  delete _interpreter;
}

std::string SV3_1aSplitterParser::getGrammarFileName() const {
  return "SV3_1aSplitterParser.g4";
}

const std::vector<std::string>& SV3_1aSplitterParser::getRuleNames() const {
  return _ruleNames;
}

dfa::Vocabulary& SV3_1aSplitterParser::getVocabulary() const {
  return _vocabulary;
}


//----------------- Source_textContext ------------------------------------------------------------------

SV3_1aSplitterParser::Source_textContext::Source_textContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<SV3_1aSplitterParser::DescriptionContext *> SV3_1aSplitterParser::Source_textContext::description() {
  return getRuleContexts<SV3_1aSplitterParser::DescriptionContext>();
}

SV3_1aSplitterParser::DescriptionContext* SV3_1aSplitterParser::Source_textContext::description(size_t i) {
  return getRuleContext<SV3_1aSplitterParser::DescriptionContext>(i);
}


size_t SV3_1aSplitterParser::Source_textContext::getRuleIndex() const {
  return SV3_1aSplitterParser::RuleSource_text;
}

void SV3_1aSplitterParser::Source_textContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterSource_text(this);
}

void SV3_1aSplitterParser::Source_textContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitSource_text(this);
}

SV3_1aSplitterParser::Source_textContext* SV3_1aSplitterParser::source_text() {
  Source_textContext *_localctx = _tracker.createInstance<Source_textContext>(_ctx, getState());
  enterRule(_localctx, 0, SV3_1aSplitterParser::RuleSource_text);
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
    setState(37);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while ((((_la & ~ 0x3fULL) == 0) &&
      ((1ULL << _la) & ((1ULL << SV3_1aSplitterParser::MODULE)
      | (1ULL << SV3_1aSplitterParser::ENDMODULE)
      | (1ULL << SV3_1aSplitterParser::INTERFACE)
      | (1ULL << SV3_1aSplitterParser::ENDINTERFACE)
      | (1ULL << SV3_1aSplitterParser::PROGRAM)
      | (1ULL << SV3_1aSplitterParser::ENDPROGRAM)
      | (1ULL << SV3_1aSplitterParser::PRIMITIVE)
      | (1ULL << SV3_1aSplitterParser::ENDPRIMITIVE)
      | (1ULL << SV3_1aSplitterParser::PACKAGE)
      | (1ULL << SV3_1aSplitterParser::ENDPACKAGE)
      | (1ULL << SV3_1aSplitterParser::CHECKER)
      | (1ULL << SV3_1aSplitterParser::ENDCHECKER)
      | (1ULL << SV3_1aSplitterParser::CONFIG)
      | (1ULL << SV3_1aSplitterParser::ENDCONFIG)
      | (1ULL << SV3_1aSplitterParser::ANY))) != 0)) {
      setState(34);
      description();
      setState(39);
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

//----------------- DescriptionContext ------------------------------------------------------------------

SV3_1aSplitterParser::DescriptionContext::DescriptionContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

SV3_1aSplitterParser::ModuleContext* SV3_1aSplitterParser::DescriptionContext::module() {
  return getRuleContext<SV3_1aSplitterParser::ModuleContext>(0);
}

SV3_1aSplitterParser::EndmoduleContext* SV3_1aSplitterParser::DescriptionContext::endmodule() {
  return getRuleContext<SV3_1aSplitterParser::EndmoduleContext>(0);
}

SV3_1aSplitterParser::Sv_interfaceContext* SV3_1aSplitterParser::DescriptionContext::sv_interface() {
  return getRuleContext<SV3_1aSplitterParser::Sv_interfaceContext>(0);
}

SV3_1aSplitterParser::EndinterfaceContext* SV3_1aSplitterParser::DescriptionContext::endinterface() {
  return getRuleContext<SV3_1aSplitterParser::EndinterfaceContext>(0);
}

SV3_1aSplitterParser::ProgramContext* SV3_1aSplitterParser::DescriptionContext::program() {
  return getRuleContext<SV3_1aSplitterParser::ProgramContext>(0);
}

SV3_1aSplitterParser::EndprogramContext* SV3_1aSplitterParser::DescriptionContext::endprogram() {
  return getRuleContext<SV3_1aSplitterParser::EndprogramContext>(0);
}

SV3_1aSplitterParser::PrimitiveContext* SV3_1aSplitterParser::DescriptionContext::primitive() {
  return getRuleContext<SV3_1aSplitterParser::PrimitiveContext>(0);
}

SV3_1aSplitterParser::EndprimitiveContext* SV3_1aSplitterParser::DescriptionContext::endprimitive() {
  return getRuleContext<SV3_1aSplitterParser::EndprimitiveContext>(0);
}

SV3_1aSplitterParser::Sv_packageContext* SV3_1aSplitterParser::DescriptionContext::sv_package() {
  return getRuleContext<SV3_1aSplitterParser::Sv_packageContext>(0);
}

SV3_1aSplitterParser::EndpackageContext* SV3_1aSplitterParser::DescriptionContext::endpackage() {
  return getRuleContext<SV3_1aSplitterParser::EndpackageContext>(0);
}

SV3_1aSplitterParser::CheckerContext* SV3_1aSplitterParser::DescriptionContext::checker() {
  return getRuleContext<SV3_1aSplitterParser::CheckerContext>(0);
}

SV3_1aSplitterParser::EndcheckerContext* SV3_1aSplitterParser::DescriptionContext::endchecker() {
  return getRuleContext<SV3_1aSplitterParser::EndcheckerContext>(0);
}

SV3_1aSplitterParser::ConfigContext* SV3_1aSplitterParser::DescriptionContext::config() {
  return getRuleContext<SV3_1aSplitterParser::ConfigContext>(0);
}

SV3_1aSplitterParser::EndconfigContext* SV3_1aSplitterParser::DescriptionContext::endconfig() {
  return getRuleContext<SV3_1aSplitterParser::EndconfigContext>(0);
}

tree::TerminalNode* SV3_1aSplitterParser::DescriptionContext::ANY() {
  return getToken(SV3_1aSplitterParser::ANY, 0);
}


size_t SV3_1aSplitterParser::DescriptionContext::getRuleIndex() const {
  return SV3_1aSplitterParser::RuleDescription;
}

void SV3_1aSplitterParser::DescriptionContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterDescription(this);
}

void SV3_1aSplitterParser::DescriptionContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitDescription(this);
}

SV3_1aSplitterParser::DescriptionContext* SV3_1aSplitterParser::description() {
  DescriptionContext *_localctx = _tracker.createInstance<DescriptionContext>(_ctx, getState());
  enterRule(_localctx, 2, SV3_1aSplitterParser::RuleDescription);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    setState(55);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case SV3_1aSplitterParser::MODULE: {
        enterOuterAlt(_localctx, 1);
        setState(40);
        module();
        break;
      }

      case SV3_1aSplitterParser::ENDMODULE: {
        enterOuterAlt(_localctx, 2);
        setState(41);
        endmodule();
        break;
      }

      case SV3_1aSplitterParser::INTERFACE: {
        enterOuterAlt(_localctx, 3);
        setState(42);
        sv_interface();
        break;
      }

      case SV3_1aSplitterParser::ENDINTERFACE: {
        enterOuterAlt(_localctx, 4);
        setState(43);
        endinterface();
        break;
      }

      case SV3_1aSplitterParser::PROGRAM: {
        enterOuterAlt(_localctx, 5);
        setState(44);
        program();
        break;
      }

      case SV3_1aSplitterParser::ENDPROGRAM: {
        enterOuterAlt(_localctx, 6);
        setState(45);
        endprogram();
        break;
      }

      case SV3_1aSplitterParser::PRIMITIVE: {
        enterOuterAlt(_localctx, 7);
        setState(46);
        primitive();
        break;
      }

      case SV3_1aSplitterParser::ENDPRIMITIVE: {
        enterOuterAlt(_localctx, 8);
        setState(47);
        endprimitive();
        break;
      }

      case SV3_1aSplitterParser::PACKAGE: {
        enterOuterAlt(_localctx, 9);
        setState(48);
        sv_package();
        break;
      }

      case SV3_1aSplitterParser::ENDPACKAGE: {
        enterOuterAlt(_localctx, 10);
        setState(49);
        endpackage();
        break;
      }

      case SV3_1aSplitterParser::CHECKER: {
        enterOuterAlt(_localctx, 11);
        setState(50);
        checker();
        break;
      }

      case SV3_1aSplitterParser::ENDCHECKER: {
        enterOuterAlt(_localctx, 12);
        setState(51);
        endchecker();
        break;
      }

      case SV3_1aSplitterParser::CONFIG: {
        enterOuterAlt(_localctx, 13);
        setState(52);
        config();
        break;
      }

      case SV3_1aSplitterParser::ENDCONFIG: {
        enterOuterAlt(_localctx, 14);
        setState(53);
        endconfig();
        break;
      }

      case SV3_1aSplitterParser::ANY: {
        enterOuterAlt(_localctx, 15);
        setState(54);
        match(SV3_1aSplitterParser::ANY);
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

//----------------- ModuleContext ------------------------------------------------------------------

SV3_1aSplitterParser::ModuleContext::ModuleContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aSplitterParser::ModuleContext::MODULE() {
  return getToken(SV3_1aSplitterParser::MODULE, 0);
}


size_t SV3_1aSplitterParser::ModuleContext::getRuleIndex() const {
  return SV3_1aSplitterParser::RuleModule;
}

void SV3_1aSplitterParser::ModuleContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterModule(this);
}

void SV3_1aSplitterParser::ModuleContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitModule(this);
}

SV3_1aSplitterParser::ModuleContext* SV3_1aSplitterParser::module() {
  ModuleContext *_localctx = _tracker.createInstance<ModuleContext>(_ctx, getState());
  enterRule(_localctx, 4, SV3_1aSplitterParser::RuleModule);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(57);
    match(SV3_1aSplitterParser::MODULE);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- EndmoduleContext ------------------------------------------------------------------

SV3_1aSplitterParser::EndmoduleContext::EndmoduleContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aSplitterParser::EndmoduleContext::ENDMODULE() {
  return getToken(SV3_1aSplitterParser::ENDMODULE, 0);
}


size_t SV3_1aSplitterParser::EndmoduleContext::getRuleIndex() const {
  return SV3_1aSplitterParser::RuleEndmodule;
}

void SV3_1aSplitterParser::EndmoduleContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterEndmodule(this);
}

void SV3_1aSplitterParser::EndmoduleContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitEndmodule(this);
}

SV3_1aSplitterParser::EndmoduleContext* SV3_1aSplitterParser::endmodule() {
  EndmoduleContext *_localctx = _tracker.createInstance<EndmoduleContext>(_ctx, getState());
  enterRule(_localctx, 6, SV3_1aSplitterParser::RuleEndmodule);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(59);
    match(SV3_1aSplitterParser::ENDMODULE);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Sv_interfaceContext ------------------------------------------------------------------

SV3_1aSplitterParser::Sv_interfaceContext::Sv_interfaceContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aSplitterParser::Sv_interfaceContext::INTERFACE() {
  return getToken(SV3_1aSplitterParser::INTERFACE, 0);
}


size_t SV3_1aSplitterParser::Sv_interfaceContext::getRuleIndex() const {
  return SV3_1aSplitterParser::RuleSv_interface;
}

void SV3_1aSplitterParser::Sv_interfaceContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterSv_interface(this);
}

void SV3_1aSplitterParser::Sv_interfaceContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitSv_interface(this);
}

SV3_1aSplitterParser::Sv_interfaceContext* SV3_1aSplitterParser::sv_interface() {
  Sv_interfaceContext *_localctx = _tracker.createInstance<Sv_interfaceContext>(_ctx, getState());
  enterRule(_localctx, 8, SV3_1aSplitterParser::RuleSv_interface);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(61);
    match(SV3_1aSplitterParser::INTERFACE);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- EndinterfaceContext ------------------------------------------------------------------

SV3_1aSplitterParser::EndinterfaceContext::EndinterfaceContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aSplitterParser::EndinterfaceContext::ENDINTERFACE() {
  return getToken(SV3_1aSplitterParser::ENDINTERFACE, 0);
}


size_t SV3_1aSplitterParser::EndinterfaceContext::getRuleIndex() const {
  return SV3_1aSplitterParser::RuleEndinterface;
}

void SV3_1aSplitterParser::EndinterfaceContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterEndinterface(this);
}

void SV3_1aSplitterParser::EndinterfaceContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitEndinterface(this);
}

SV3_1aSplitterParser::EndinterfaceContext* SV3_1aSplitterParser::endinterface() {
  EndinterfaceContext *_localctx = _tracker.createInstance<EndinterfaceContext>(_ctx, getState());
  enterRule(_localctx, 10, SV3_1aSplitterParser::RuleEndinterface);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(63);
    match(SV3_1aSplitterParser::ENDINTERFACE);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- ProgramContext ------------------------------------------------------------------

SV3_1aSplitterParser::ProgramContext::ProgramContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aSplitterParser::ProgramContext::PROGRAM() {
  return getToken(SV3_1aSplitterParser::PROGRAM, 0);
}


size_t SV3_1aSplitterParser::ProgramContext::getRuleIndex() const {
  return SV3_1aSplitterParser::RuleProgram;
}

void SV3_1aSplitterParser::ProgramContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterProgram(this);
}

void SV3_1aSplitterParser::ProgramContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitProgram(this);
}

SV3_1aSplitterParser::ProgramContext* SV3_1aSplitterParser::program() {
  ProgramContext *_localctx = _tracker.createInstance<ProgramContext>(_ctx, getState());
  enterRule(_localctx, 12, SV3_1aSplitterParser::RuleProgram);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(65);
    match(SV3_1aSplitterParser::PROGRAM);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- EndprogramContext ------------------------------------------------------------------

SV3_1aSplitterParser::EndprogramContext::EndprogramContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aSplitterParser::EndprogramContext::ENDPROGRAM() {
  return getToken(SV3_1aSplitterParser::ENDPROGRAM, 0);
}


size_t SV3_1aSplitterParser::EndprogramContext::getRuleIndex() const {
  return SV3_1aSplitterParser::RuleEndprogram;
}

void SV3_1aSplitterParser::EndprogramContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterEndprogram(this);
}

void SV3_1aSplitterParser::EndprogramContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitEndprogram(this);
}

SV3_1aSplitterParser::EndprogramContext* SV3_1aSplitterParser::endprogram() {
  EndprogramContext *_localctx = _tracker.createInstance<EndprogramContext>(_ctx, getState());
  enterRule(_localctx, 14, SV3_1aSplitterParser::RuleEndprogram);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(67);
    match(SV3_1aSplitterParser::ENDPROGRAM);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- PrimitiveContext ------------------------------------------------------------------

SV3_1aSplitterParser::PrimitiveContext::PrimitiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aSplitterParser::PrimitiveContext::PRIMITIVE() {
  return getToken(SV3_1aSplitterParser::PRIMITIVE, 0);
}


size_t SV3_1aSplitterParser::PrimitiveContext::getRuleIndex() const {
  return SV3_1aSplitterParser::RulePrimitive;
}

void SV3_1aSplitterParser::PrimitiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterPrimitive(this);
}

void SV3_1aSplitterParser::PrimitiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitPrimitive(this);
}

SV3_1aSplitterParser::PrimitiveContext* SV3_1aSplitterParser::primitive() {
  PrimitiveContext *_localctx = _tracker.createInstance<PrimitiveContext>(_ctx, getState());
  enterRule(_localctx, 16, SV3_1aSplitterParser::RulePrimitive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(69);
    match(SV3_1aSplitterParser::PRIMITIVE);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- EndprimitiveContext ------------------------------------------------------------------

SV3_1aSplitterParser::EndprimitiveContext::EndprimitiveContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aSplitterParser::EndprimitiveContext::ENDPRIMITIVE() {
  return getToken(SV3_1aSplitterParser::ENDPRIMITIVE, 0);
}


size_t SV3_1aSplitterParser::EndprimitiveContext::getRuleIndex() const {
  return SV3_1aSplitterParser::RuleEndprimitive;
}

void SV3_1aSplitterParser::EndprimitiveContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterEndprimitive(this);
}

void SV3_1aSplitterParser::EndprimitiveContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitEndprimitive(this);
}

SV3_1aSplitterParser::EndprimitiveContext* SV3_1aSplitterParser::endprimitive() {
  EndprimitiveContext *_localctx = _tracker.createInstance<EndprimitiveContext>(_ctx, getState());
  enterRule(_localctx, 18, SV3_1aSplitterParser::RuleEndprimitive);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(71);
    match(SV3_1aSplitterParser::ENDPRIMITIVE);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Sv_packageContext ------------------------------------------------------------------

SV3_1aSplitterParser::Sv_packageContext::Sv_packageContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aSplitterParser::Sv_packageContext::PACKAGE() {
  return getToken(SV3_1aSplitterParser::PACKAGE, 0);
}


size_t SV3_1aSplitterParser::Sv_packageContext::getRuleIndex() const {
  return SV3_1aSplitterParser::RuleSv_package;
}

void SV3_1aSplitterParser::Sv_packageContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterSv_package(this);
}

void SV3_1aSplitterParser::Sv_packageContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitSv_package(this);
}

SV3_1aSplitterParser::Sv_packageContext* SV3_1aSplitterParser::sv_package() {
  Sv_packageContext *_localctx = _tracker.createInstance<Sv_packageContext>(_ctx, getState());
  enterRule(_localctx, 20, SV3_1aSplitterParser::RuleSv_package);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(73);
    match(SV3_1aSplitterParser::PACKAGE);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- EndpackageContext ------------------------------------------------------------------

SV3_1aSplitterParser::EndpackageContext::EndpackageContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aSplitterParser::EndpackageContext::ENDPACKAGE() {
  return getToken(SV3_1aSplitterParser::ENDPACKAGE, 0);
}


size_t SV3_1aSplitterParser::EndpackageContext::getRuleIndex() const {
  return SV3_1aSplitterParser::RuleEndpackage;
}

void SV3_1aSplitterParser::EndpackageContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterEndpackage(this);
}

void SV3_1aSplitterParser::EndpackageContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitEndpackage(this);
}

SV3_1aSplitterParser::EndpackageContext* SV3_1aSplitterParser::endpackage() {
  EndpackageContext *_localctx = _tracker.createInstance<EndpackageContext>(_ctx, getState());
  enterRule(_localctx, 22, SV3_1aSplitterParser::RuleEndpackage);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(75);
    match(SV3_1aSplitterParser::ENDPACKAGE);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- CheckerContext ------------------------------------------------------------------

SV3_1aSplitterParser::CheckerContext::CheckerContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aSplitterParser::CheckerContext::CHECKER() {
  return getToken(SV3_1aSplitterParser::CHECKER, 0);
}


size_t SV3_1aSplitterParser::CheckerContext::getRuleIndex() const {
  return SV3_1aSplitterParser::RuleChecker;
}

void SV3_1aSplitterParser::CheckerContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterChecker(this);
}

void SV3_1aSplitterParser::CheckerContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitChecker(this);
}

SV3_1aSplitterParser::CheckerContext* SV3_1aSplitterParser::checker() {
  CheckerContext *_localctx = _tracker.createInstance<CheckerContext>(_ctx, getState());
  enterRule(_localctx, 24, SV3_1aSplitterParser::RuleChecker);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(77);
    match(SV3_1aSplitterParser::CHECKER);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- EndcheckerContext ------------------------------------------------------------------

SV3_1aSplitterParser::EndcheckerContext::EndcheckerContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aSplitterParser::EndcheckerContext::ENDCHECKER() {
  return getToken(SV3_1aSplitterParser::ENDCHECKER, 0);
}


size_t SV3_1aSplitterParser::EndcheckerContext::getRuleIndex() const {
  return SV3_1aSplitterParser::RuleEndchecker;
}

void SV3_1aSplitterParser::EndcheckerContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterEndchecker(this);
}

void SV3_1aSplitterParser::EndcheckerContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitEndchecker(this);
}

SV3_1aSplitterParser::EndcheckerContext* SV3_1aSplitterParser::endchecker() {
  EndcheckerContext *_localctx = _tracker.createInstance<EndcheckerContext>(_ctx, getState());
  enterRule(_localctx, 26, SV3_1aSplitterParser::RuleEndchecker);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(79);
    match(SV3_1aSplitterParser::ENDCHECKER);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- ConfigContext ------------------------------------------------------------------

SV3_1aSplitterParser::ConfigContext::ConfigContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aSplitterParser::ConfigContext::CONFIG() {
  return getToken(SV3_1aSplitterParser::CONFIG, 0);
}


size_t SV3_1aSplitterParser::ConfigContext::getRuleIndex() const {
  return SV3_1aSplitterParser::RuleConfig;
}

void SV3_1aSplitterParser::ConfigContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterConfig(this);
}

void SV3_1aSplitterParser::ConfigContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitConfig(this);
}

SV3_1aSplitterParser::ConfigContext* SV3_1aSplitterParser::config() {
  ConfigContext *_localctx = _tracker.createInstance<ConfigContext>(_ctx, getState());
  enterRule(_localctx, 28, SV3_1aSplitterParser::RuleConfig);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(81);
    match(SV3_1aSplitterParser::CONFIG);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- EndconfigContext ------------------------------------------------------------------

SV3_1aSplitterParser::EndconfigContext::EndconfigContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aSplitterParser::EndconfigContext::ENDCONFIG() {
  return getToken(SV3_1aSplitterParser::ENDCONFIG, 0);
}


size_t SV3_1aSplitterParser::EndconfigContext::getRuleIndex() const {
  return SV3_1aSplitterParser::RuleEndconfig;
}

void SV3_1aSplitterParser::EndconfigContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterEndconfig(this);
}

void SV3_1aSplitterParser::EndconfigContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitEndconfig(this);
}

SV3_1aSplitterParser::EndconfigContext* SV3_1aSplitterParser::endconfig() {
  EndconfigContext *_localctx = _tracker.createInstance<EndconfigContext>(_ctx, getState());
  enterRule(_localctx, 30, SV3_1aSplitterParser::RuleEndconfig);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(83);
    match(SV3_1aSplitterParser::ENDCONFIG);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- AnyContext ------------------------------------------------------------------

SV3_1aSplitterParser::AnyContext::AnyContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SV3_1aSplitterParser::AnyContext::ANY() {
  return getToken(SV3_1aSplitterParser::ANY, 0);
}


size_t SV3_1aSplitterParser::AnyContext::getRuleIndex() const {
  return SV3_1aSplitterParser::RuleAny;
}

void SV3_1aSplitterParser::AnyContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterAny(this);
}

void SV3_1aSplitterParser::AnyContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<SV3_1aSplitterParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitAny(this);
}

SV3_1aSplitterParser::AnyContext* SV3_1aSplitterParser::any() {
  AnyContext *_localctx = _tracker.createInstance<AnyContext>(_ctx, getState());
  enterRule(_localctx, 32, SV3_1aSplitterParser::RuleAny);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(85);
    match(SV3_1aSplitterParser::ANY);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

// Static vars and initialization.
std::vector<dfa::DFA> SV3_1aSplitterParser::_decisionToDFA;
atn::PredictionContextCache SV3_1aSplitterParser::_sharedContextCache;

// We own the ATN which in turn owns the ATN states.
atn::ATN SV3_1aSplitterParser::_atn;
std::vector<uint16_t> SV3_1aSplitterParser::_serializedATN;

std::vector<std::string> SV3_1aSplitterParser::_ruleNames = {
  "source_text", "description", "module", "endmodule", "sv_interface", "endinterface", 
  "program", "endprogram", "primitive", "endprimitive", "sv_package", "endpackage", 
  "checker", "endchecker", "config", "endconfig", "any"
};

std::vector<std::string> SV3_1aSplitterParser::_literalNames = {
  "", "", "", "'module'", "'endmodule'", "'interface'", "'endinterface'", 
  "'program'", "'endprogram'", "'primivite'", "'endprimitive'", "'package'", 
  "'endpackage'", "'checker'", "'endchecker'", "'config'", "'endconfig'"
};

std::vector<std::string> SV3_1aSplitterParser::_symbolicNames = {
  "", "One_line_comment", "Block_comment", "MODULE", "ENDMODULE", "INTERFACE", 
  "ENDINTERFACE", "PROGRAM", "ENDPROGRAM", "PRIMITIVE", "ENDPRIMITIVE", 
  "PACKAGE", "ENDPACKAGE", "CHECKER", "ENDCHECKER", "CONFIG", "ENDCONFIG", 
  "String", "Spaces", "CR", "ANY"
};

dfa::Vocabulary SV3_1aSplitterParser::_vocabulary(_literalNames, _symbolicNames);

std::vector<std::string> SV3_1aSplitterParser::_tokenNames;

SV3_1aSplitterParser::Initializer::Initializer() {
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
    0x3, 0x16, 0x5a, 0x4, 0x2, 0x9, 0x2, 0x4, 0x3, 0x9, 0x3, 0x4, 0x4, 0x9, 
    0x4, 0x4, 0x5, 0x9, 0x5, 0x4, 0x6, 0x9, 0x6, 0x4, 0x7, 0x9, 0x7, 0x4, 
    0x8, 0x9, 0x8, 0x4, 0x9, 0x9, 0x9, 0x4, 0xa, 0x9, 0xa, 0x4, 0xb, 0x9, 
    0xb, 0x4, 0xc, 0x9, 0xc, 0x4, 0xd, 0x9, 0xd, 0x4, 0xe, 0x9, 0xe, 0x4, 
    0xf, 0x9, 0xf, 0x4, 0x10, 0x9, 0x10, 0x4, 0x11, 0x9, 0x11, 0x4, 0x12, 
    0x9, 0x12, 0x3, 0x2, 0x7, 0x2, 0x26, 0xa, 0x2, 0xc, 0x2, 0xe, 0x2, 0x29, 
    0xb, 0x2, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 
    0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 
    0x3, 0x3, 0x3, 0x3, 0x5, 0x3, 0x3a, 0xa, 0x3, 0x3, 0x4, 0x3, 0x4, 0x3, 
    0x5, 0x3, 0x5, 0x3, 0x6, 0x3, 0x6, 0x3, 0x7, 0x3, 0x7, 0x3, 0x8, 0x3, 
    0x8, 0x3, 0x9, 0x3, 0x9, 0x3, 0xa, 0x3, 0xa, 0x3, 0xb, 0x3, 0xb, 0x3, 
    0xc, 0x3, 0xc, 0x3, 0xd, 0x3, 0xd, 0x3, 0xe, 0x3, 0xe, 0x3, 0xf, 0x3, 
    0xf, 0x3, 0x10, 0x3, 0x10, 0x3, 0x11, 0x3, 0x11, 0x3, 0x12, 0x3, 0x12, 
    0x3, 0x12, 0x2, 0x2, 0x13, 0x2, 0x4, 0x6, 0x8, 0xa, 0xc, 0xe, 0x10, 
    0x12, 0x14, 0x16, 0x18, 0x1a, 0x1c, 0x1e, 0x20, 0x22, 0x2, 0x2, 0x2, 
    0x57, 0x2, 0x27, 0x3, 0x2, 0x2, 0x2, 0x4, 0x39, 0x3, 0x2, 0x2, 0x2, 
    0x6, 0x3b, 0x3, 0x2, 0x2, 0x2, 0x8, 0x3d, 0x3, 0x2, 0x2, 0x2, 0xa, 0x3f, 
    0x3, 0x2, 0x2, 0x2, 0xc, 0x41, 0x3, 0x2, 0x2, 0x2, 0xe, 0x43, 0x3, 0x2, 
    0x2, 0x2, 0x10, 0x45, 0x3, 0x2, 0x2, 0x2, 0x12, 0x47, 0x3, 0x2, 0x2, 
    0x2, 0x14, 0x49, 0x3, 0x2, 0x2, 0x2, 0x16, 0x4b, 0x3, 0x2, 0x2, 0x2, 
    0x18, 0x4d, 0x3, 0x2, 0x2, 0x2, 0x1a, 0x4f, 0x3, 0x2, 0x2, 0x2, 0x1c, 
    0x51, 0x3, 0x2, 0x2, 0x2, 0x1e, 0x53, 0x3, 0x2, 0x2, 0x2, 0x20, 0x55, 
    0x3, 0x2, 0x2, 0x2, 0x22, 0x57, 0x3, 0x2, 0x2, 0x2, 0x24, 0x26, 0x5, 
    0x4, 0x3, 0x2, 0x25, 0x24, 0x3, 0x2, 0x2, 0x2, 0x26, 0x29, 0x3, 0x2, 
    0x2, 0x2, 0x27, 0x25, 0x3, 0x2, 0x2, 0x2, 0x27, 0x28, 0x3, 0x2, 0x2, 
    0x2, 0x28, 0x3, 0x3, 0x2, 0x2, 0x2, 0x29, 0x27, 0x3, 0x2, 0x2, 0x2, 
    0x2a, 0x3a, 0x5, 0x6, 0x4, 0x2, 0x2b, 0x3a, 0x5, 0x8, 0x5, 0x2, 0x2c, 
    0x3a, 0x5, 0xa, 0x6, 0x2, 0x2d, 0x3a, 0x5, 0xc, 0x7, 0x2, 0x2e, 0x3a, 
    0x5, 0xe, 0x8, 0x2, 0x2f, 0x3a, 0x5, 0x10, 0x9, 0x2, 0x30, 0x3a, 0x5, 
    0x12, 0xa, 0x2, 0x31, 0x3a, 0x5, 0x14, 0xb, 0x2, 0x32, 0x3a, 0x5, 0x16, 
    0xc, 0x2, 0x33, 0x3a, 0x5, 0x18, 0xd, 0x2, 0x34, 0x3a, 0x5, 0x1a, 0xe, 
    0x2, 0x35, 0x3a, 0x5, 0x1c, 0xf, 0x2, 0x36, 0x3a, 0x5, 0x1e, 0x10, 0x2, 
    0x37, 0x3a, 0x5, 0x20, 0x11, 0x2, 0x38, 0x3a, 0x7, 0x16, 0x2, 0x2, 0x39, 
    0x2a, 0x3, 0x2, 0x2, 0x2, 0x39, 0x2b, 0x3, 0x2, 0x2, 0x2, 0x39, 0x2c, 
    0x3, 0x2, 0x2, 0x2, 0x39, 0x2d, 0x3, 0x2, 0x2, 0x2, 0x39, 0x2e, 0x3, 
    0x2, 0x2, 0x2, 0x39, 0x2f, 0x3, 0x2, 0x2, 0x2, 0x39, 0x30, 0x3, 0x2, 
    0x2, 0x2, 0x39, 0x31, 0x3, 0x2, 0x2, 0x2, 0x39, 0x32, 0x3, 0x2, 0x2, 
    0x2, 0x39, 0x33, 0x3, 0x2, 0x2, 0x2, 0x39, 0x34, 0x3, 0x2, 0x2, 0x2, 
    0x39, 0x35, 0x3, 0x2, 0x2, 0x2, 0x39, 0x36, 0x3, 0x2, 0x2, 0x2, 0x39, 
    0x37, 0x3, 0x2, 0x2, 0x2, 0x39, 0x38, 0x3, 0x2, 0x2, 0x2, 0x3a, 0x5, 
    0x3, 0x2, 0x2, 0x2, 0x3b, 0x3c, 0x7, 0x5, 0x2, 0x2, 0x3c, 0x7, 0x3, 
    0x2, 0x2, 0x2, 0x3d, 0x3e, 0x7, 0x6, 0x2, 0x2, 0x3e, 0x9, 0x3, 0x2, 
    0x2, 0x2, 0x3f, 0x40, 0x7, 0x7, 0x2, 0x2, 0x40, 0xb, 0x3, 0x2, 0x2, 
    0x2, 0x41, 0x42, 0x7, 0x8, 0x2, 0x2, 0x42, 0xd, 0x3, 0x2, 0x2, 0x2, 
    0x43, 0x44, 0x7, 0x9, 0x2, 0x2, 0x44, 0xf, 0x3, 0x2, 0x2, 0x2, 0x45, 
    0x46, 0x7, 0xa, 0x2, 0x2, 0x46, 0x11, 0x3, 0x2, 0x2, 0x2, 0x47, 0x48, 
    0x7, 0xb, 0x2, 0x2, 0x48, 0x13, 0x3, 0x2, 0x2, 0x2, 0x49, 0x4a, 0x7, 
    0xc, 0x2, 0x2, 0x4a, 0x15, 0x3, 0x2, 0x2, 0x2, 0x4b, 0x4c, 0x7, 0xd, 
    0x2, 0x2, 0x4c, 0x17, 0x3, 0x2, 0x2, 0x2, 0x4d, 0x4e, 0x7, 0xe, 0x2, 
    0x2, 0x4e, 0x19, 0x3, 0x2, 0x2, 0x2, 0x4f, 0x50, 0x7, 0xf, 0x2, 0x2, 
    0x50, 0x1b, 0x3, 0x2, 0x2, 0x2, 0x51, 0x52, 0x7, 0x10, 0x2, 0x2, 0x52, 
    0x1d, 0x3, 0x2, 0x2, 0x2, 0x53, 0x54, 0x7, 0x11, 0x2, 0x2, 0x54, 0x1f, 
    0x3, 0x2, 0x2, 0x2, 0x55, 0x56, 0x7, 0x12, 0x2, 0x2, 0x56, 0x21, 0x3, 
    0x2, 0x2, 0x2, 0x57, 0x58, 0x7, 0x16, 0x2, 0x2, 0x58, 0x23, 0x3, 0x2, 
    0x2, 0x2, 0x4, 0x27, 0x39, 
  };

  atn::ATNDeserializer deserializer;
  _atn = deserializer.deserialize(_serializedATN);

  size_t count = _atn.getNumberOfDecisions();
  _decisionToDFA.reserve(count);
  for (size_t i = 0; i < count; i++) { 
    _decisionToDFA.emplace_back(_atn.getDecisionState(i), i);
  }
}

SV3_1aSplitterParser::Initializer SV3_1aSplitterParser::_init;
