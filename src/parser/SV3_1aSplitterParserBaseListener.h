
// Generated from SV3_1aSplitterParser.g4 by ANTLR 4.9.1

#pragma once


#include "antlr4-runtime.h"
#include "SV3_1aSplitterParserListener.h"


/**
 * This class provides an empty implementation of SV3_1aSplitterParserListener,
 * which can be extended to create a listener which only needs to handle a subset
 * of the available methods.
 */
class  SV3_1aSplitterParserBaseListener : public SV3_1aSplitterParserListener {
public:

  virtual void enterSource_text(SV3_1aSplitterParser::Source_textContext * /*ctx*/) override { }
  virtual void exitSource_text(SV3_1aSplitterParser::Source_textContext * /*ctx*/) override { }

  virtual void enterDescription(SV3_1aSplitterParser::DescriptionContext * /*ctx*/) override { }
  virtual void exitDescription(SV3_1aSplitterParser::DescriptionContext * /*ctx*/) override { }

  virtual void enterModule(SV3_1aSplitterParser::ModuleContext * /*ctx*/) override { }
  virtual void exitModule(SV3_1aSplitterParser::ModuleContext * /*ctx*/) override { }

  virtual void enterEndmodule(SV3_1aSplitterParser::EndmoduleContext * /*ctx*/) override { }
  virtual void exitEndmodule(SV3_1aSplitterParser::EndmoduleContext * /*ctx*/) override { }

  virtual void enterSv_interface(SV3_1aSplitterParser::Sv_interfaceContext * /*ctx*/) override { }
  virtual void exitSv_interface(SV3_1aSplitterParser::Sv_interfaceContext * /*ctx*/) override { }

  virtual void enterEndinterface(SV3_1aSplitterParser::EndinterfaceContext * /*ctx*/) override { }
  virtual void exitEndinterface(SV3_1aSplitterParser::EndinterfaceContext * /*ctx*/) override { }

  virtual void enterProgram(SV3_1aSplitterParser::ProgramContext * /*ctx*/) override { }
  virtual void exitProgram(SV3_1aSplitterParser::ProgramContext * /*ctx*/) override { }

  virtual void enterEndprogram(SV3_1aSplitterParser::EndprogramContext * /*ctx*/) override { }
  virtual void exitEndprogram(SV3_1aSplitterParser::EndprogramContext * /*ctx*/) override { }

  virtual void enterPrimitive(SV3_1aSplitterParser::PrimitiveContext * /*ctx*/) override { }
  virtual void exitPrimitive(SV3_1aSplitterParser::PrimitiveContext * /*ctx*/) override { }

  virtual void enterEndprimitive(SV3_1aSplitterParser::EndprimitiveContext * /*ctx*/) override { }
  virtual void exitEndprimitive(SV3_1aSplitterParser::EndprimitiveContext * /*ctx*/) override { }

  virtual void enterSv_package(SV3_1aSplitterParser::Sv_packageContext * /*ctx*/) override { }
  virtual void exitSv_package(SV3_1aSplitterParser::Sv_packageContext * /*ctx*/) override { }

  virtual void enterEndpackage(SV3_1aSplitterParser::EndpackageContext * /*ctx*/) override { }
  virtual void exitEndpackage(SV3_1aSplitterParser::EndpackageContext * /*ctx*/) override { }

  virtual void enterChecker(SV3_1aSplitterParser::CheckerContext * /*ctx*/) override { }
  virtual void exitChecker(SV3_1aSplitterParser::CheckerContext * /*ctx*/) override { }

  virtual void enterEndchecker(SV3_1aSplitterParser::EndcheckerContext * /*ctx*/) override { }
  virtual void exitEndchecker(SV3_1aSplitterParser::EndcheckerContext * /*ctx*/) override { }

  virtual void enterConfig(SV3_1aSplitterParser::ConfigContext * /*ctx*/) override { }
  virtual void exitConfig(SV3_1aSplitterParser::ConfigContext * /*ctx*/) override { }

  virtual void enterEndconfig(SV3_1aSplitterParser::EndconfigContext * /*ctx*/) override { }
  virtual void exitEndconfig(SV3_1aSplitterParser::EndconfigContext * /*ctx*/) override { }

  virtual void enterAny(SV3_1aSplitterParser::AnyContext * /*ctx*/) override { }
  virtual void exitAny(SV3_1aSplitterParser::AnyContext * /*ctx*/) override { }


  virtual void enterEveryRule(antlr4::ParserRuleContext * /*ctx*/) override { }
  virtual void exitEveryRule(antlr4::ParserRuleContext * /*ctx*/) override { }
  virtual void visitTerminal(antlr4::tree::TerminalNode * /*node*/) override { }
  virtual void visitErrorNode(antlr4::tree::ErrorNode * /*node*/) override { }

};

