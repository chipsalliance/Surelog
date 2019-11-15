
// Generated from /home/alain/Surelog/src/../grammar/SV3_1aSplitterParser.g4 by ANTLR 4.7.2

#pragma once


#include "antlr4-runtime.h"
#include "SV3_1aSplitterParserVisitor.h"


/**
 * This class provides an empty implementation of SV3_1aSplitterParserVisitor, which can be
 * extended to create a visitor which only needs to handle a subset of the available methods.
 */
class  SV3_1aSplitterParserBaseVisitor : public SV3_1aSplitterParserVisitor {
public:

  virtual antlrcpp::Any visitSource_text(SV3_1aSplitterParser::Source_textContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitDescription(SV3_1aSplitterParser::DescriptionContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitModule(SV3_1aSplitterParser::ModuleContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitEndmodule(SV3_1aSplitterParser::EndmoduleContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitSv_interface(SV3_1aSplitterParser::Sv_interfaceContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitEndinterface(SV3_1aSplitterParser::EndinterfaceContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitProgram(SV3_1aSplitterParser::ProgramContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitEndprogram(SV3_1aSplitterParser::EndprogramContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitPrimitive(SV3_1aSplitterParser::PrimitiveContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitEndprimitive(SV3_1aSplitterParser::EndprimitiveContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitSv_package(SV3_1aSplitterParser::Sv_packageContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitEndpackage(SV3_1aSplitterParser::EndpackageContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitChecker(SV3_1aSplitterParser::CheckerContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitEndchecker(SV3_1aSplitterParser::EndcheckerContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitConfig(SV3_1aSplitterParser::ConfigContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitEndconfig(SV3_1aSplitterParser::EndconfigContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitAny(SV3_1aSplitterParser::AnyContext *ctx) override {
    return visitChildren(ctx);
  }


};

