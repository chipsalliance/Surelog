
// Generated from SV3_1aSplitterParser.g4 by ANTLR 4.9.1

#pragma once


#include "antlr4-runtime.h"
#include "SV3_1aSplitterParser.h"


/**
 * This interface defines an abstract listener for a parse tree produced by SV3_1aSplitterParser.
 */
class  SV3_1aSplitterParserListener : public antlr4::tree::ParseTreeListener {
public:

  virtual void enterSource_text(SV3_1aSplitterParser::Source_textContext *ctx) = 0;
  virtual void exitSource_text(SV3_1aSplitterParser::Source_textContext *ctx) = 0;

  virtual void enterDescription(SV3_1aSplitterParser::DescriptionContext *ctx) = 0;
  virtual void exitDescription(SV3_1aSplitterParser::DescriptionContext *ctx) = 0;

  virtual void enterModule(SV3_1aSplitterParser::ModuleContext *ctx) = 0;
  virtual void exitModule(SV3_1aSplitterParser::ModuleContext *ctx) = 0;

  virtual void enterEndmodule(SV3_1aSplitterParser::EndmoduleContext *ctx) = 0;
  virtual void exitEndmodule(SV3_1aSplitterParser::EndmoduleContext *ctx) = 0;

  virtual void enterSv_interface(SV3_1aSplitterParser::Sv_interfaceContext *ctx) = 0;
  virtual void exitSv_interface(SV3_1aSplitterParser::Sv_interfaceContext *ctx) = 0;

  virtual void enterEndinterface(SV3_1aSplitterParser::EndinterfaceContext *ctx) = 0;
  virtual void exitEndinterface(SV3_1aSplitterParser::EndinterfaceContext *ctx) = 0;

  virtual void enterProgram(SV3_1aSplitterParser::ProgramContext *ctx) = 0;
  virtual void exitProgram(SV3_1aSplitterParser::ProgramContext *ctx) = 0;

  virtual void enterEndprogram(SV3_1aSplitterParser::EndprogramContext *ctx) = 0;
  virtual void exitEndprogram(SV3_1aSplitterParser::EndprogramContext *ctx) = 0;

  virtual void enterPrimitive(SV3_1aSplitterParser::PrimitiveContext *ctx) = 0;
  virtual void exitPrimitive(SV3_1aSplitterParser::PrimitiveContext *ctx) = 0;

  virtual void enterEndprimitive(SV3_1aSplitterParser::EndprimitiveContext *ctx) = 0;
  virtual void exitEndprimitive(SV3_1aSplitterParser::EndprimitiveContext *ctx) = 0;

  virtual void enterSv_package(SV3_1aSplitterParser::Sv_packageContext *ctx) = 0;
  virtual void exitSv_package(SV3_1aSplitterParser::Sv_packageContext *ctx) = 0;

  virtual void enterEndpackage(SV3_1aSplitterParser::EndpackageContext *ctx) = 0;
  virtual void exitEndpackage(SV3_1aSplitterParser::EndpackageContext *ctx) = 0;

  virtual void enterChecker(SV3_1aSplitterParser::CheckerContext *ctx) = 0;
  virtual void exitChecker(SV3_1aSplitterParser::CheckerContext *ctx) = 0;

  virtual void enterEndchecker(SV3_1aSplitterParser::EndcheckerContext *ctx) = 0;
  virtual void exitEndchecker(SV3_1aSplitterParser::EndcheckerContext *ctx) = 0;

  virtual void enterConfig(SV3_1aSplitterParser::ConfigContext *ctx) = 0;
  virtual void exitConfig(SV3_1aSplitterParser::ConfigContext *ctx) = 0;

  virtual void enterEndconfig(SV3_1aSplitterParser::EndconfigContext *ctx) = 0;
  virtual void exitEndconfig(SV3_1aSplitterParser::EndconfigContext *ctx) = 0;

  virtual void enterAny(SV3_1aSplitterParser::AnyContext *ctx) = 0;
  virtual void exitAny(SV3_1aSplitterParser::AnyContext *ctx) = 0;


};

