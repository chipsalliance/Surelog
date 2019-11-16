
// Generated from /home/alain/Surelog/grammar/SV3_1aSplitterParser.g4 by ANTLR 4.7.2

#pragma once


#include "antlr4-runtime.h"
#include "SV3_1aSplitterParser.h"



/**
 * This class defines an abstract visitor for a parse tree
 * produced by SV3_1aSplitterParser.
 */
class  SV3_1aSplitterParserVisitor : public antlr4::tree::AbstractParseTreeVisitor {
public:

  /**
   * Visit parse trees produced by SV3_1aSplitterParser.
   */
    virtual antlrcpp::Any visitSource_text(SV3_1aSplitterParser::Source_textContext *context) = 0;

    virtual antlrcpp::Any visitDescription(SV3_1aSplitterParser::DescriptionContext *context) = 0;

    virtual antlrcpp::Any visitModule(SV3_1aSplitterParser::ModuleContext *context) = 0;

    virtual antlrcpp::Any visitEndmodule(SV3_1aSplitterParser::EndmoduleContext *context) = 0;

    virtual antlrcpp::Any visitSv_interface(SV3_1aSplitterParser::Sv_interfaceContext *context) = 0;

    virtual antlrcpp::Any visitEndinterface(SV3_1aSplitterParser::EndinterfaceContext *context) = 0;

    virtual antlrcpp::Any visitProgram(SV3_1aSplitterParser::ProgramContext *context) = 0;

    virtual antlrcpp::Any visitEndprogram(SV3_1aSplitterParser::EndprogramContext *context) = 0;

    virtual antlrcpp::Any visitPrimitive(SV3_1aSplitterParser::PrimitiveContext *context) = 0;

    virtual antlrcpp::Any visitEndprimitive(SV3_1aSplitterParser::EndprimitiveContext *context) = 0;

    virtual antlrcpp::Any visitSv_package(SV3_1aSplitterParser::Sv_packageContext *context) = 0;

    virtual antlrcpp::Any visitEndpackage(SV3_1aSplitterParser::EndpackageContext *context) = 0;

    virtual antlrcpp::Any visitChecker(SV3_1aSplitterParser::CheckerContext *context) = 0;

    virtual antlrcpp::Any visitEndchecker(SV3_1aSplitterParser::EndcheckerContext *context) = 0;

    virtual antlrcpp::Any visitConfig(SV3_1aSplitterParser::ConfigContext *context) = 0;

    virtual antlrcpp::Any visitEndconfig(SV3_1aSplitterParser::EndconfigContext *context) = 0;

    virtual antlrcpp::Any visitAny(SV3_1aSplitterParser::AnyContext *context) = 0;


};

