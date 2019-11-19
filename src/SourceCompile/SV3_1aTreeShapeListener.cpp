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

/*
 * File:   SV3_1aTreeShapeListener.cpp
 * Author: alain
 *
 * Created on April 16, 2017, 8:28 PM
 */

#include "SourceCompile/SymbolTable.h"
#include "CommandLine/CommandLineParser.hpp"
#include "ErrorReporting/ErrorContainer.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/Compiler.h"
#include "SourceCompile/ParseFile.h"
#include "Utils/StringUtils.h"

#include <cstdlib>
#include <iostream>
#include <regex>
#include "antlr4-runtime.h"

using namespace std;
using namespace antlr4;
using namespace SURELOG;

#include "parser/SV3_1aLexer.h"
#include "parser/SV3_1aParser.h"
#include "parser/SV3_1aParserBaseListener.h"
#include "parser/SV3_1aPpParserBaseListener.h"
#include "Utils/ParseUtils.h"
#include "Utils/FileUtils.h"
#include "SourceCompile/SV3_1aPpTreeShapeListener.h"
#include "SourceCompile/SV3_1aTreeShapeListener.h"
#include "SourceCompile/SV3_1aTreeShapeHelper.h"
using namespace antlr4;

void SV3_1aTreeShapeListener::enterTop_level_rule(
    SV3_1aParser::Top_level_ruleContext * /*ctx*/) {
  if (m_pf->getFileContent() == NULL) {
    m_fileContent = new FileContent(
        m_pf->getFileId(0), m_pf->getLibrary(),
        m_pf->getCompileSourceFile()->getSymbolTable(),
        m_pf->getCompileSourceFile()->getErrorContainer(), NULL, 0);
    m_pf->setFileContent(m_fileContent);
    m_pf->getCompileSourceFile()->getCompiler()->getDesign()->addFileContent(
        m_pf->getFileId(0), m_fileContent);
  } else {
    m_fileContent = m_pf->getFileContent();
  }
  IncludeFileInfo info(1, m_pf->getFileId(0), 0, 1);
  m_includeFileInfo.push(info);
}

void SV3_1aTreeShapeListener::enterTop_level_library_rule(
    SV3_1aParser::Top_level_library_ruleContext * /*ctx*/) {
  // Visited from Library/SVLibShapeListener.h
  m_fileContent = new FileContent(m_pf->getFileId(0), m_pf->getLibrary(),
                                  m_pf->getSymbolTable(),
                                  m_pf->getErrorContainer(), NULL, 0);
  m_pf->setFileContent(m_fileContent);
}

void SV3_1aTreeShapeListener::enterModule_declaration(
    SV3_1aParser::Module_declarationContext *ctx) {
  std::string ident;
  if (ctx->module_ansi_header())
    ident = ctx->module_ansi_header()->identifier()->getText();
  else if (ctx->module_nonansi_header())
    ident = ctx->module_nonansi_header()->identifier()->getText();
  else {
    if (ctx->identifier(0))
      ident = ctx->identifier(0)->getText();
    else
      ident = "MODULE NAME UNKNOWN";
  }
  ident = std::regex_replace(ident, std::regex(EscapeSequence), "");
  addNestedDesignElement(ctx, ident, DesignElement::Module,
                         VObjectType::slModule);
}

void SV3_1aTreeShapeListener::exitModule_declaration(
    SV3_1aParser::Module_declarationContext *ctx) {
  addVObject(ctx, VObjectType::slModule_declaration);
  if (ctx->EXTERN()) m_nestedElements.pop();
}

void SV3_1aTreeShapeListener::enterEndmodule(
    SV3_1aParser::EndmoduleContext * /*ctx*/) {
  m_nestedElements.pop();
}

void SV3_1aTreeShapeListener::enterSlline(
    SV3_1aParser::SllineContext * /*ctx*/) {}

void SV3_1aTreeShapeListener::exitSlline(SV3_1aParser::SllineContext *ctx) {
  unsigned int startLine = atoi(ctx->Integral_number()[0]->getText().c_str());
  int type = atoi(ctx->Integral_number()[1]->getText().c_str());
  std::string file = ctx->String()->getText();
  StringUtils::ltrim(file, '\"');
  StringUtils::rtrim(file, '\"');
  std::pair<int, int> lineCol = ParseUtils::getLineColumn(m_tokens, ctx);
  if (type == 1) {
    // Push
    IncludeFileInfo info(startLine,
                         m_pf->getSymbolTable()->registerSymbol(file),
                         lineCol.first, type);
    m_includeFileInfo.push(info);
  } else if (type == 2) {
    // Pop
    if (m_includeFileInfo.size()) m_includeFileInfo.pop();
    if (m_includeFileInfo.size()) {
      m_includeFileInfo.top().m_sectionFile =
          m_pf->getSymbolTable()->registerSymbol(file);
      m_includeFileInfo.top().m_originalLine = lineCol.first /*+ m_lineOffset*/;
      m_includeFileInfo.top().m_sectionStartLine = startLine;
      m_includeFileInfo.top().m_type = type;
    }
  }
}

void SV3_1aTreeShapeListener::enterInterface_declaration(
    SV3_1aParser::Interface_declarationContext *ctx) {
  std::string ident;
  if (ctx->interface_ansi_header())
    ident = ctx->interface_ansi_header()->interface_identifier()->getText();
  else if (ctx->interface_nonansi_header())
    ident = ctx->interface_nonansi_header()->interface_identifier()->getText();
  else {
    if (ctx->interface_identifier(0))
      ident = ctx->interface_identifier(0)->getText();
    else
      ident = "INTERFACE NAME UNKNOWN";
  }
  ident = std::regex_replace(ident, std::regex(EscapeSequence), "");
  addNestedDesignElement(ctx, ident, DesignElement::Interface,
                         VObjectType::slInterface);
}

void SV3_1aTreeShapeListener::exitInterface_declaration(
    SV3_1aParser::Interface_declarationContext *ctx) {
  addVObject(ctx, VObjectType::slInterface_declaration);
  if (ctx->EXTERN()) m_nestedElements.pop();
}

void SV3_1aTreeShapeListener::enterEndinterface(
    SV3_1aParser::EndinterfaceContext * /*ctx*/) {
  m_nestedElements.pop();
}

void SV3_1aTreeShapeListener::enterProgram_declaration(
    SV3_1aParser::Program_declarationContext *ctx) {
  std::string ident;
  if (ctx->program_ansi_header())
    ident = ctx->program_ansi_header()->identifier()->getText();
  else if (ctx->program_nonansi_header())
    ident = ctx->program_nonansi_header()->identifier()->getText();
  else {
    if (ctx->identifier(0))
      ident = ctx->identifier(0)->getText();
    else
      ident = "PROGRAM NAME UNKNOWN";
  }
  ident = std::regex_replace(ident, std::regex(EscapeSequence), "");
  addDesignElement(ctx, ident, DesignElement::Program, VObjectType::slProgram);
}

void SV3_1aTreeShapeListener::enterClass_declaration(
    SV3_1aParser::Class_declarationContext *ctx) {
  std::string ident;
  if (ctx->identifier(0)) {
    ident = ctx->identifier(0)->getText();
    ident = std::regex_replace(ident, std::regex(EscapeSequence), "");
    addDesignElement(ctx, ident, DesignElement::Class, VObjectType::slClass);
  } else
    addDesignElement(ctx, "UNNAMED_CLASS", DesignElement::Class,
                     VObjectType::slClass);
}

SV3_1aTreeShapeListener::SV3_1aTreeShapeListener(
    ParseFile *pf, antlr4::CommonTokenStream *tokens, unsigned int lineOffset)
    : SV3_1aTreeShapeHelper::SV3_1aTreeShapeHelper(pf, tokens, lineOffset) {}

SV3_1aTreeShapeListener::~SV3_1aTreeShapeListener() {}

void SV3_1aTreeShapeListener::enterPackage_declaration(
    SV3_1aParser::Package_declarationContext *ctx) {
  std::string ident = ctx->identifier(0)->getText();
  ident = std::regex_replace(ident, std::regex(EscapeSequence), "");
  addDesignElement(ctx, ident, DesignElement::Package, VObjectType::slPackage);
}

void SV3_1aTreeShapeListener::enterTimeUnitsDecl_TimeUnit(
    SV3_1aParser::TimeUnitsDecl_TimeUnitContext *ctx) {
  if (m_currentElement) {
    m_currentElement->m_timeInfo.m_type = TimeInfo::TimeUnitTimePrecision;
    auto pair = getTimeValue(ctx->time_literal());
    m_currentElement->m_timeInfo.m_timeUnitValue = pair.first;
    m_currentElement->m_timeInfo.m_timeUnit = pair.second;
  }
}

void SV3_1aTreeShapeListener::enterTimeUnitsDecl_TimePrecision(
    SV3_1aParser::TimeUnitsDecl_TimePrecisionContext *ctx) {
  if (m_currentElement) {
    m_currentElement->m_timeInfo.m_type = TimeInfo::TimeUnitTimePrecision;
    auto pair = getTimeValue(ctx->time_literal());
    m_currentElement->m_timeInfo.m_timePrecisionValue = pair.first;
    m_currentElement->m_timeInfo.m_timePrecision = pair.second;
  }
}

void SV3_1aTreeShapeListener::enterTimeUnitsDecl_TimeUnitTimePrecision(
    SV3_1aParser::TimeUnitsDecl_TimeUnitTimePrecisionContext *ctx) {
  if (m_currentElement) {
    m_currentElement->m_timeInfo.m_type = TimeInfo::TimeUnitTimePrecision;
    auto pair = getTimeValue(ctx->time_literal(0));
    m_currentElement->m_timeInfo.m_timeUnitValue = pair.first;
    m_currentElement->m_timeInfo.m_timeUnit = pair.second;
    pair = getTimeValue(ctx->time_literal(1));
    m_currentElement->m_timeInfo.m_timePrecisionValue = pair.first;
    m_currentElement->m_timeInfo.m_timePrecision = pair.second;
  }
}

void SV3_1aTreeShapeListener::enterTimeUnitsDecl_TimeUnitDiv(
    SV3_1aParser::TimeUnitsDecl_TimeUnitDivContext *ctx) {
  if (m_currentElement) {
    m_currentElement->m_timeInfo.m_type = TimeInfo::TimeUnitTimePrecision;
    auto pair = getTimeValue(ctx->time_literal(0));
    m_currentElement->m_timeInfo.m_timeUnitValue = pair.first;
    m_currentElement->m_timeInfo.m_timeUnit = pair.second;
    pair = getTimeValue(ctx->time_literal(1));
    m_currentElement->m_timeInfo.m_timePrecisionValue = pair.first;
    m_currentElement->m_timeInfo.m_timePrecision = pair.second;
  }
}

void SV3_1aTreeShapeListener::enterTimeUnitsDecl_TimePrecisionTimeUnit(
    SV3_1aParser::TimeUnitsDecl_TimePrecisionTimeUnitContext *ctx) {
  if (m_currentElement) {
    m_currentElement->m_timeInfo.m_type = TimeInfo::TimeUnitTimePrecision;
    auto pair = getTimeValue(ctx->time_literal(1));
    m_currentElement->m_timeInfo.m_timeUnitValue = pair.first;
    m_currentElement->m_timeInfo.m_timeUnit = pair.second;
    pair = getTimeValue(ctx->time_literal(0));
    m_currentElement->m_timeInfo.m_timePrecisionValue = pair.first;
    m_currentElement->m_timeInfo.m_timePrecision = pair.second;
  }
}

void SV3_1aTreeShapeListener::enterUdp_nonansi_declaration(
    SV3_1aParser::Udp_nonansi_declarationContext *ctx) {
  std::string ident = ctx->identifier()->getText();
  ident = std::regex_replace(ident, std::regex(EscapeSequence), "");
  addDesignElement(ctx, ident, DesignElement::Primitive,
                   VObjectType::slPrimitive);
}

void SV3_1aTreeShapeListener::enterUdp_ansi_declaration(
    SV3_1aParser::Udp_ansi_declarationContext *ctx) {
  std::string ident = ctx->identifier()->getText();
  ident = std::regex_replace(ident, std::regex(EscapeSequence), "");
  addDesignElement(ctx, ident, DesignElement::Primitive,
                   VObjectType::slPrimitive);
}

void SV3_1aTreeShapeListener::enterSurelog_macro_not_defined(
    SV3_1aParser::Surelog_macro_not_definedContext *ctx) {
  std::string text = ctx->getText();
  text.erase(0, 26);
  text.erase(text.size() - 3, text.size() - 1);
  logError(ErrorDefinition::PA_UNKOWN_MACRO, ctx, text);
}

void SV3_1aTreeShapeListener::exitNumber_Integral(
    SV3_1aParser::Number_IntegralContext *ctx) {
  auto number = ctx->Integral_number();
  addVObject(ctx, number->getText(),
             VObjectType::slIntConst);  // TODO: Octal, Hexa...
}

void SV3_1aTreeShapeListener::exitNumber_Real(
    SV3_1aParser::Number_RealContext *ctx) {
  addVObject(ctx, ctx->Real_number()->getText(), VObjectType::slRealConst);
}

void SV3_1aTreeShapeListener::exitUnbased_unsized_literal(
    SV3_1aParser::Unbased_unsized_literalContext *ctx) {
  if (ctx->TICK_0())
    addVObject(ctx, ctx->TICK_0()->getText(), VObjectType::sl0);
  else if (ctx->TICK_1())
    addVObject(ctx, ctx->TICK_1()->getText(), VObjectType::sl1);
  else {
    std::string s = ctx->Simple_identifier()->getText();
    VObjectType type = VObjectType::slZ;
    if (s == "z" || s == "Z") {
      type = VObjectType::slZ;
    } else if (s == "x" || s == "X") {
      type = VObjectType::slX;
    }
    addVObject(ctx, s, type);
  }
}

/*
void
SV3_1aTreeShapeListener::exitComment_OneLine
(SV3_1aParser::Comment_OneLineContext *ctx)
{
  addVObject (ctx, ctx->One_line_comment ()->getText (),
VObjectType::slComments);
}

void
SV3_1aTreeShapeListener::exitComment_Block (SV3_1aParser::Comment_BlockContext
*ctx)
{
  addVObject (ctx, ctx->Block_comment ()->getText (), VObjectType::slComments);
}
*/

void SV3_1aTreeShapeListener::exitString_value(
    SV3_1aParser::String_valueContext *ctx) {
  std::string ident;

  ident = ctx->String()->getText();

  addVObject(ctx, ident, VObjectType::slStringLiteral);

  if (ident.size() > SV_MAX_STRING_SIZE) {
    logError(ErrorDefinition::PA_MAX_LENGTH_IDENTIFIER, ctx, ident);
  }
}

void SV3_1aTreeShapeListener::exitIdentifier(
    SV3_1aParser::IdentifierContext *ctx) {
  std::string ident;
  if (ctx->Simple_identifier())
    ident = ctx->Simple_identifier()->getText();
  else if (ctx->Escaped_identifier()) {
    ident = ctx->Escaped_identifier()->getText();
    ident.erase(0, 3);
    ident.erase(ident.size() - 3, 3);
  } else if (ctx->THIS())
    ident = ctx->THIS()->getText();
  else if (ctx->RANDOMIZE())
    ident = ctx->RANDOMIZE()->getText();
  else if (ctx->SAMPLE())
    ident = ctx->SAMPLE()->getText();
  else if (ctx->LOGIC()) {
    ident = ctx->LOGIC()->getText();
    // if (getVerilogVersion () == SystemVerilog)
    //  logError (ErrorDefinition::PA_RESERVED_KEYWORD, ctx, ident);
  } else if (ctx->NEW()) {
    ident = ctx->NEW()->getText();
  } else if (ctx->BIT()) {
    ident = ctx->BIT()->getText();
  } else if (ctx->BYTE()) {
    ident = ctx->BYTE()->getText();
  } else if (ctx->EXPECT()) {
    ident = ctx->EXPECT()->getText();
  } else if (ctx->VAR()) {
    ident = ctx->VAR()->getText();
  } else if (ctx->DO()) {
    ident = ctx->DO()->getText();
  } else if (ctx->SIGNED()) {
    ident = ctx->SIGNED()->getText();
  } else if (ctx->UNSIGNED()) {
    ident = ctx->UNSIGNED()->getText();
  } else if (ctx->FINAL()) {
    ident = ctx->FINAL()->getText();
  } else if (ctx->GLOBAL()) {
    ident = ctx->GLOBAL()->getText();
  } else if (ctx->SOFT()) {
    ident = ctx->SOFT()->getText();
  } else if (ctx->CONTEXT()) {
    ident = ctx->CONTEXT()->getText();
  }
  // !!! Don't forget to change CompileModule.cpp type checker !!!
  addVObject(ctx, ident, VObjectType::slStringConst);

  if (ident.size() > SV_MAX_IDENTIFIER_SIZE) {
    logError(ErrorDefinition::PA_MAX_LENGTH_IDENTIFIER, ctx, ident);
  }
}

void SV3_1aTreeShapeListener::exitClass_type(
    SV3_1aParser::Class_typeContext *ctx) {
  std::string ident;
  ParserRuleContext *childCtx = NULL;
  if (ctx->Simple_identifier()) {
    childCtx = (ParserRuleContext *)ctx->Simple_identifier();
    ident = ctx->Simple_identifier()->getText();
  } else if (ctx->Escaped_identifier()) {
    childCtx = (ParserRuleContext *)ctx->Escaped_identifier();
    ident = ctx->Escaped_identifier()->getText();
    ident.erase(0, 3);
    ident.erase(ident.size() - 3, 3);
  } else if (ctx->THIS()) {
    childCtx = (ParserRuleContext *)ctx->THIS();
    ident = ctx->THIS()->getText();
  } else if (ctx->RANDOMIZE()) {
    childCtx = (ParserRuleContext *)ctx->RANDOMIZE();
    ident = ctx->RANDOMIZE()->getText();
  } else if (ctx->SAMPLE()) {
    childCtx = (ParserRuleContext *)ctx->SAMPLE();
    ident = ctx->SAMPLE()->getText();
  } else if (ctx->DOLLAR_UNIT()) {
    childCtx = (ParserRuleContext *)ctx->DOLLAR_UNIT();
    ident = ctx->DOLLAR_UNIT()->getText();
  }
  addVObject(childCtx, ident, VObjectType::slStringConst);
  addVObject(ctx, VObjectType::slClass_type);

  if (ident.size() > SV_MAX_IDENTIFIER_SIZE) {
    logError(ErrorDefinition::PA_MAX_LENGTH_IDENTIFIER, ctx, ident);
  }
}

void SV3_1aTreeShapeListener::exitHierarchical_identifier(
    SV3_1aParser::Hierarchical_identifierContext *ctx) {
  std::string ident;
  ParserRuleContext *childCtx = NULL;

  childCtx = (ParserRuleContext *)ctx->children[0];
  ident = ctx->getText();
  ident = std::regex_replace(ident, std::regex(EscapeSequence), "");
  addVObject(childCtx, ident, VObjectType::slStringConst);
  addVObject(ctx, VObjectType::slHierarchical_identifier);

  if (ident.size() > SV_MAX_IDENTIFIER_SIZE) {
    logError(ErrorDefinition::PA_MAX_LENGTH_IDENTIFIER, ctx, ident);
  }
}

void SV3_1aTreeShapeListener::exitFile_path_spec(
    SV3_1aParser::File_path_specContext *ctx) {
  std::string ident;
  ident = ctx->getText();

  addVObject(ctx, ident, VObjectType::slStringConst);

  if (ident.size() > SV_MAX_IDENTIFIER_SIZE) {
    logError(ErrorDefinition::PA_MAX_LENGTH_IDENTIFIER, ctx, ident);
  }
}

void SV3_1aTreeShapeListener::exitPackage_scope(
    SV3_1aParser::Package_scopeContext *ctx) {}

void SV3_1aTreeShapeListener::enterUnconnected_drive_directive(
    SV3_1aParser::Unconnected_drive_directiveContext *ctx) {}

void SV3_1aTreeShapeListener::enterNounconnected_drive_directive(
    SV3_1aParser::Nounconnected_drive_directiveContext *ctx) {}

void SV3_1aTreeShapeListener::enterEveryRule(antlr4::ParserRuleContext *ctx) {}
void SV3_1aTreeShapeListener::exitEveryRule(antlr4::ParserRuleContext *ctx) {}
void SV3_1aTreeShapeListener::visitTerminal(antlr4::tree::TerminalNode *node) {}
void SV3_1aTreeShapeListener::visitErrorNode(antlr4::tree::ErrorNode *node) {}

void SV3_1aTreeShapeListener::exitBegin_keywords_directive(
    SV3_1aParser::Begin_keywords_directiveContext *ctx) {
  std::string version = ctx->String()->getText();
  if (version == "\"1364-1995\"") {
    setVerilogVersion(Verilog1995);
  } else if (version == "\"1364-2001\"") {
    setVerilogVersion(Verilog2001);
  } else if (version == "\"1364-2005\"") {
    setVerilogVersion(Verilog2005);
  } else if (version == "\"1800-2005\"") {
    setVerilogVersion(Verilog2005);
  } else if (version == "\"1800-2009\"") {
    setVerilogVersion(Verilog2009);
  } else if (version == "\"1800-2012\"") {
    setVerilogVersion(SystemVerilog);
  } else if (version == "\"1800-2017\"") {
    setVerilogVersion(SystemVerilog);
  } else {
    logError(ErrorDefinition::PA_UNSUPPORTED_KEYWORD_LIST, ctx, version);
  }
}

void SV3_1aTreeShapeListener::exitEnd_keywords_directive(
    SV3_1aParser::End_keywords_directiveContext *ctx) {
  setVerilogVersion(SystemVerilog);
}
