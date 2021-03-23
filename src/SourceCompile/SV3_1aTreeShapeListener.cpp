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
#include "CommandLine/CommandLineParser.h"
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
  m_nestedElements.pop();
}

void SV3_1aTreeShapeListener::exitClass_constructor_declaration(SV3_1aParser::Class_constructor_declarationContext * ctx) {
  if (ctx->ENDFUNCTION())
    addVObject((ParserRuleContext*) ctx->ENDFUNCTION(), VObjectType::slEndfunction);
  addVObject (ctx, VObjectType::slClass_constructor_declaration);
}

void SV3_1aTreeShapeListener::exitFunction_body_declaration(SV3_1aParser::Function_body_declarationContext * ctx) {
  if (ctx->ENDFUNCTION())
    addVObject((ParserRuleContext*) ctx->ENDFUNCTION(), VObjectType::slEndfunction);
  addVObject (ctx, VObjectType::slFunction_body_declaration);
}

void SV3_1aTreeShapeListener::exitTask_body_declaration(SV3_1aParser::Task_body_declarationContext * ctx) {
  if (ctx->ENDTASK())
    addVObject((ParserRuleContext*) ctx->ENDTASK(), VObjectType::slEndtask);
  addVObject (ctx, VObjectType::slTask_body_declaration);
}

void SV3_1aTreeShapeListener::exitJump_statement(SV3_1aParser::Jump_statementContext * ctx) {
  if (ctx->BREAK()) {
    addVObject((ParserRuleContext*) ctx->BREAK(), VObjectType::slBreakStmt);
  } else if (ctx->CONTINUE()) {
    addVObject((ParserRuleContext*) ctx->CONTINUE(), VObjectType::slContinueStmt);
  } else if (ctx->RETURN()) {
    addVObject((ParserRuleContext*) ctx->RETURN(), VObjectType::slReturnStmt);
  }
  addVObject (ctx, VObjectType::slJump_statement);
}

void SV3_1aTreeShapeListener::exitClass_declaration(SV3_1aParser::Class_declarationContext * ctx) {
  if (ctx->VIRTUAL())
    addVObject ((ParserRuleContext*) ctx->VIRTUAL(), VObjectType::slVirtual);
  if (ctx->IMPLEMENTS())
    addVObject ((ParserRuleContext*) ctx->IMPLEMENTS(), VObjectType::slImplements);
  if (ctx->EXTENDS())
    addVObject ((ParserRuleContext*) ctx->EXTENDS(), VObjectType::slExtends);
  if (ctx->ENDCLASS())
    addVObject ((ParserRuleContext*) ctx->ENDCLASS(), VObjectType::slEndclass);
  addVObject (ctx, VObjectType::slClass_declaration);
}

void SV3_1aTreeShapeListener::exitInterface_class_declaration(SV3_1aParser::Interface_class_declarationContext * ctx)  {
  if (ctx->EXTENDS())
    addVObject ((ParserRuleContext*) ctx->EXTENDS(), VObjectType::slExtends);
  if (ctx->ENDCLASS())
    addVObject ((ParserRuleContext*) ctx->ENDCLASS(), VObjectType::slEndclass);
  addVObject (ctx, VObjectType::slInterface_class_declaration);
}

void SV3_1aTreeShapeListener::exitChecker_declaration(SV3_1aParser::Checker_declarationContext * ctx) {
  if (ctx->ENDCHECKER())
    addVObject ((ParserRuleContext*) ctx->ENDCHECKER(), VObjectType::slEndchecker);
  addVObject (ctx, VObjectType::slChecker_declaration);
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
  if (ctx->EXTERN() == NULL)
    if (ctx->ENDINTERFACE())
      addVObject ((ParserRuleContext*) ctx->ENDINTERFACE(), VObjectType::slEndinterface);
  addVObject(ctx, VObjectType::slInterface_declaration);
  m_nestedElements.pop();
}

void SV3_1aTreeShapeListener::exitProperty_expr(SV3_1aParser::Property_exprContext * ctx) {
  if (ctx->CASE()) {
    addVObject ((ParserRuleContext*) ctx->CASE(), VObjectType::slCase);
  }
  if (ctx->ENDCASE()) {
    addVObject ((ParserRuleContext*) ctx->ENDCASE(), VObjectType::slEndcase);
  } else if (ctx->OR()) {
    addVObject ((ParserRuleContext*) ctx->OR(), VObjectType::slOR);
  } else if (ctx->AND()) {
    addVObject ((ParserRuleContext*) ctx->AND(), VObjectType::slAND);
  } else if (ctx->IF()) {
    addVObject ((ParserRuleContext*) ctx->IF(), VObjectType::slIF);
  } else if (ctx->STRONG()) {
    addVObject ((ParserRuleContext*) ctx->STRONG(), VObjectType::slSTRONG);
  } else if (ctx->WEAK()) {
    addVObject ((ParserRuleContext*) ctx->WEAK(), VObjectType::slWEAK);
  } else if (ctx->NOT()) {
    addVObject ((ParserRuleContext*) ctx->NOT(), VObjectType::slNOT);
  } else if (ctx->OVERLAP_IMPLY()) {
    addVObject ((ParserRuleContext*) ctx->OVERLAP_IMPLY(), VObjectType::slOVERLAP_IMPLY);
  } else if (ctx->NON_OVERLAP_IMPLY()) {
    addVObject ((ParserRuleContext*) ctx->NON_OVERLAP_IMPLY(), VObjectType::slNON_OVERLAP_IMPLY);
  } else if (ctx->OVERLAPPED()) {
    addVObject ((ParserRuleContext*) ctx->OVERLAPPED(), VObjectType::slOVERLAPPED);
  } else if (ctx->NONOVERLAPPED()) {
    addVObject ((ParserRuleContext*) ctx->NONOVERLAPPED(), VObjectType::slNONOVERLAPPED);
  } else if (ctx->S_NEXTTIME()) {
    addVObject ((ParserRuleContext*) ctx->S_NEXTTIME(), VObjectType::slS_NEXTTIME);
  } else if (ctx->ALWAYS()) {
    addVObject ((ParserRuleContext*) ctx->ALWAYS(), VObjectType::slALWAYS);
  } else if (ctx->S_ALWAYS()) {
    addVObject ((ParserRuleContext*) ctx->S_ALWAYS(), VObjectType::slS_ALWAYS);
  } else if (ctx->S_EVENTUALLY()) {
    addVObject ((ParserRuleContext*) ctx->S_EVENTUALLY(), VObjectType::slS_EVENTUALLY);
  } else if (ctx->EVENTUALLY()) {
    addVObject ((ParserRuleContext*) ctx->EVENTUALLY(), VObjectType::slEVENTUALLY);
  } else if (ctx->UNTIL()) {
    addVObject ((ParserRuleContext*) ctx->UNTIL(), VObjectType::slUNTIL);
  } else if (ctx->S_UNTIL()) {
    addVObject ((ParserRuleContext*) ctx->S_UNTIL(), VObjectType::slS_UNTIL);
  } else if (ctx->IMPLIES()) {
    addVObject ((ParserRuleContext*) ctx->IMPLIES(), VObjectType::slIMPLIES);
  } else if (ctx->IFF()) {
    addVObject ((ParserRuleContext*) ctx->IFF(), VObjectType::slIFF);
  } else if (ctx->ACCEPT_ON()) {
    addVObject ((ParserRuleContext*) ctx->ACCEPT_ON(), VObjectType::slACCEPT_ON);
  } else if (ctx->REJECT_ON()) {
    addVObject ((ParserRuleContext*) ctx->REJECT_ON(), VObjectType::slREJECT_ON);
  } else if (ctx->SYNC_ACCEPT_ON()) {
    addVObject ((ParserRuleContext*) ctx->SYNC_ACCEPT_ON(), VObjectType::slSYNC_ACCEPT_ON);
  } else if (ctx->SYNC_REJECT_ON()) {
    addVObject ((ParserRuleContext*) ctx->SYNC_REJECT_ON(), VObjectType::slSYNC_REJECT_ON);
  }       
  addVObject (ctx, VObjectType::slProperty_expr);
}

void SV3_1aTreeShapeListener::exitGenerate_module_case_statement(SV3_1aParser::Generate_module_case_statementContext * ctx) {
  if (ctx->ENDCASE())
    addVObject ((ParserRuleContext*) ctx->ENDCASE(), VObjectType::slEndcase);
  addVObject (ctx, VObjectType::slGenerate_module_case_statement);
}

void SV3_1aTreeShapeListener::exitGenerate_interface_case_statement(SV3_1aParser::Generate_interface_case_statementContext * ctx) {
  if (ctx->ENDCASE())
    addVObject ((ParserRuleContext*) ctx->ENDCASE(), VObjectType::slEndcase);
  addVObject (ctx, VObjectType::slGenerate_interface_case_statement);
}

void SV3_1aTreeShapeListener::exitCase_generate_construct(SV3_1aParser::Case_generate_constructContext * ctx) {
  if (ctx->ENDCASE())
    addVObject ((ParserRuleContext*) ctx->ENDCASE(), VObjectType::slEndcase);
  addVObject (ctx, VObjectType::slCase_generate_construct);
}

void SV3_1aTreeShapeListener::exitCase_statement(SV3_1aParser::Case_statementContext * ctx) {
  if (ctx->ENDCASE())
    addVObject ((ParserRuleContext*) ctx->ENDCASE(), VObjectType::slEndcase);
  addVObject (ctx, VObjectType::slCase_statement);
}

void SV3_1aTreeShapeListener::exitRandcase_statement(SV3_1aParser::Randcase_statementContext * ctx) {
  if (ctx->ENDCASE())
    addVObject ((ParserRuleContext*) ctx->ENDCASE(), VObjectType::slEndcase);
  addVObject (ctx, VObjectType::slRandcase_statement);
}

void SV3_1aTreeShapeListener::exitRs_case(SV3_1aParser::Rs_caseContext * ctx) {
  if (ctx->ENDCASE())
    addVObject ((ParserRuleContext*) ctx->ENDCASE(), VObjectType::slEndcase);
  addVObject (ctx, VObjectType::slRs_case);
}

void SV3_1aTreeShapeListener::exitSequence_declaration(SV3_1aParser::Sequence_declarationContext * ctx) {
  if (ctx->ENDSEQUENCE())
    addVObject ((ParserRuleContext*) ctx->ENDSEQUENCE(), VObjectType::slEndsequence);
  addVObject (ctx, VObjectType::slSequence_declaration);
}

void SV3_1aTreeShapeListener::exitRandsequence_statement(SV3_1aParser::Randsequence_statementContext * ctx) {
  if (ctx->ENDSEQUENCE())
    addVObject ((ParserRuleContext*) ctx->ENDSEQUENCE(), VObjectType::slEndsequence);
  addVObject (ctx, VObjectType::slRandsequence_statement);
}

void SV3_1aTreeShapeListener::exitSeq_block(SV3_1aParser::Seq_blockContext * ctx) {
  if (ctx->END())
    addVObject ((ParserRuleContext*) ctx->END(), VObjectType::slEnd);
  addVObject (ctx, VObjectType::slSeq_block);
}


void SV3_1aTreeShapeListener::exitGenerate_module_named_block(SV3_1aParser::Generate_module_named_blockContext * ctx) {
  if (ctx->END())
    addVObject ((ParserRuleContext*) ctx->END(), VObjectType::slEnd);
  addVObject (ctx, VObjectType::slGenerate_module_named_block);
}

void SV3_1aTreeShapeListener::exitGenerate_module_block(SV3_1aParser::Generate_module_blockContext * ctx) {
  if (ctx->END())
    addVObject ((ParserRuleContext*) ctx->END(), VObjectType::slEnd);
  addVObject (ctx, VObjectType::slGenerate_module_block);
}

void SV3_1aTreeShapeListener::exitGenerate_interface_named_block(SV3_1aParser::Generate_interface_named_blockContext * ctx)  {
  if (ctx->END())
    addVObject ((ParserRuleContext*) ctx->END(), VObjectType::slEnd);
  addVObject (ctx, VObjectType::slGenerate_interface_named_block);
}

void SV3_1aTreeShapeListener::exitGenerate_interface_block(SV3_1aParser::Generate_interface_blockContext * ctx) {
  if (ctx->END())
    addVObject ((ParserRuleContext*) ctx->END(), VObjectType::slEnd);
  addVObject (ctx, VObjectType::slGenerate_interface_block);
}

void SV3_1aTreeShapeListener::exitGenerate_block(SV3_1aParser::Generate_blockContext * ctx) {
  if (ctx->END())
    addVObject ((ParserRuleContext*) ctx->END(), VObjectType::slEnd);
  addVObject (ctx, VObjectType::slGenerate_block);
}

void SV3_1aTreeShapeListener::exitNamed_port_connection(SV3_1aParser::Named_port_connectionContext * ctx) {
  if (ctx->DOTSTAR())
    addVObject ((ParserRuleContext*) ctx->DOTSTAR(), VObjectType::slDotStar);
  if (ctx->OPEN_PARENS())
    addVObject ((ParserRuleContext*) ctx->OPEN_PARENS(), VObjectType::slOpenParens);
  if (ctx->CLOSE_PARENS())
    addVObject ((ParserRuleContext*) ctx->CLOSE_PARENS(), VObjectType::slCloseParens);  
  addVObject (ctx, VObjectType::slNamed_port_connection);
}

void SV3_1aTreeShapeListener::exitPattern(SV3_1aParser::PatternContext * ctx) {
  if (ctx->DOT())
    addVObject ((ParserRuleContext*) ctx->DOT(), VObjectType::slDot);
  else if (ctx->DOTSTAR())
    addVObject ((ParserRuleContext*) ctx->DOTSTAR(), VObjectType::slDotStar);
  else if (ctx->TAGGED())
    addVObject ((ParserRuleContext*) ctx->TAGGED(), VObjectType::slTagged);
 
  addVObject (ctx, VObjectType::slPattern);
}

void SV3_1aTreeShapeListener::exitSpecify_block(SV3_1aParser::Specify_blockContext * ctx) {
  if (ctx->ENDSPECIFY())
    addVObject ((ParserRuleContext*) ctx->ENDSPECIFY(), VObjectType::slEndspecify);
  addVObject (ctx, VObjectType::slSpecify_block);
}

void SV3_1aTreeShapeListener::exitConfig_declaration(SV3_1aParser::Config_declarationContext * ctx) {
  if (ctx->ENDCONFIG())
    addVObject ((ParserRuleContext*) ctx->ENDCONFIG(), VObjectType::slEndconfig);
  addVObject (ctx, VObjectType::slConfig_declaration);
}


void SV3_1aTreeShapeListener::exitDpi_import_export(SV3_1aParser::Dpi_import_exportContext * ctx) {
  if (ctx->IMPORT())
    addVObject ((ParserRuleContext*) ctx->IMPORT(), VObjectType::slImport);
  if (ctx->EXPORT())
    addVObject ((ParserRuleContext*) ctx->EXPORT(), VObjectType::slExport);
  addVObject (ctx, VObjectType::slDpi_import_export);
}

void SV3_1aTreeShapeListener::exitProperty_declaration(SV3_1aParser::Property_declarationContext * ctx) {
  if (ctx->ENDPROPERTY())
    addVObject ((ParserRuleContext*) ctx->ENDPROPERTY(), VObjectType::slEndproperty);
  addVObject (ctx, VObjectType::slProperty_declaration);
}

void SV3_1aTreeShapeListener::exitCovergroup_declaration(SV3_1aParser::Covergroup_declarationContext * ctx) {
  if (ctx->ENDGROUP())
    addVObject ((ParserRuleContext*) ctx->ENDGROUP(), VObjectType::slEndgroup);
  addVObject (ctx, VObjectType::slCovergroup_declaration);
}

void SV3_1aTreeShapeListener::exitGenerated_module_instantiation(SV3_1aParser::Generated_module_instantiationContext * ctx) {
 if (ctx->ENDGENERATE())
    addVObject ((ParserRuleContext*) ctx->ENDGENERATE(), VObjectType::slEndgenerate);
  addVObject (ctx, VObjectType::slGenerated_module_instantiation);
}

void SV3_1aTreeShapeListener::exitGenerated_interface_instantiation(SV3_1aParser::Generated_interface_instantiationContext * ctx)  {
  if (ctx->ENDGENERATE())
    addVObject ((ParserRuleContext*) ctx->ENDGENERATE(), VObjectType::slEndgenerate);
  addVObject (ctx, VObjectType::slGenerated_interface_instantiation);
}

void SV3_1aTreeShapeListener::exitGenerate_region(SV3_1aParser::Generate_regionContext * ctx) {
  if (ctx->ENDGENERATE())
    addVObject ((ParserRuleContext*) ctx->ENDGENERATE(), VObjectType::slEndgenerate);
  addVObject (ctx, VObjectType::slGenerate_region);
}

void SV3_1aTreeShapeListener::exitUdp_declaration(SV3_1aParser::Udp_declarationContext * ctx) {
  if (ctx->ENDPRIMITIVE())
    addVObject ((ParserRuleContext*) ctx->ENDPRIMITIVE(), VObjectType::slEndprimitive);
  addVObject (ctx, VObjectType::slUdp_declaration);
}

void SV3_1aTreeShapeListener::exitCombinational_body(SV3_1aParser::Combinational_bodyContext * ctx) {
  if (ctx->ENDTABLE())
    addVObject ((ParserRuleContext*) ctx->ENDTABLE(), VObjectType::slEndtable);
  addVObject (ctx, VObjectType::slCombinational_body);
}

void SV3_1aTreeShapeListener::exitSequential_body(SV3_1aParser::Sequential_bodyContext * ctx) {
  if (ctx->ENDTABLE())
    addVObject ((ParserRuleContext*) ctx->ENDTABLE(), VObjectType::slEndtable);
  addVObject (ctx, VObjectType::slSequential_body);
}

void SV3_1aTreeShapeListener::exitClocking_declaration(SV3_1aParser::Clocking_declarationContext * ctx) {
  if (ctx->DEFAULT())
    addVObject ((ParserRuleContext*) ctx->DEFAULT(), VObjectType::slDefault);
  if (ctx->GLOBAL())
    addVObject ((ParserRuleContext*) ctx->GLOBAL(), VObjectType::slGlobal);
  if (ctx->ENDCLOCKING())
    addVObject ((ParserRuleContext*) ctx->ENDCLOCKING(), VObjectType::slEndclocking);
  addVObject (ctx, VObjectType::slClocking_declaration);
}

void SV3_1aTreeShapeListener::exitPackage_declaration(SV3_1aParser::Package_declarationContext * ctx)  {
  if (ctx->ENDPACKAGE())
    addVObject ((ParserRuleContext*) ctx->ENDPACKAGE(), VObjectType::slEndpackage);
  addVObject (ctx, VObjectType::slPackage_declaration);
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
    m_currentElement->m_timeInfo.m_type = TimeInfo::Type::TimeUnitTimePrecision;
    auto pair = getTimeValue(ctx->time_literal());
    m_currentElement->m_timeInfo.m_timeUnitValue = pair.first;
    m_currentElement->m_timeInfo.m_timeUnit = pair.second;
  }
}

void SV3_1aTreeShapeListener::enterTimescale_directive(SV3_1aParser::Timescale_directiveContext *ctx)
{
  TimeInfo compUnitTimeInfo;
  compUnitTimeInfo.m_type = TimeInfo::Type::Timescale;
  compUnitTimeInfo.m_fileId = m_pf->getFileId(0);
  std::pair<int, int> lineCol = ParseUtils::getLineColumn(ctx->TICK_TIMESCALE());
  compUnitTimeInfo.m_line = lineCol.first;
  std::regex base_regex("`timescale([0-9]+)([mnsupf]+)/([0-9]+)([mnsupf]+)");
  std::smatch base_match;
  std::string value = ctx->getText().c_str();
  if (std::regex_match(value, base_match, base_regex)) {
    std::ssub_match base1_sub_match = base_match[1];
    std::string base1 = base1_sub_match.str();
    compUnitTimeInfo.m_timeUnitValue = atoi(base1.c_str());
    compUnitTimeInfo.m_timeUnit = TimeInfo::unitFromString(base_match[2].str());
    std::ssub_match base2_sub_match = base_match[3];
    std::string base2 = base2_sub_match.str();
    compUnitTimeInfo.m_timePrecisionValue = atoi(base2.c_str());
    compUnitTimeInfo.m_timePrecision = TimeInfo::unitFromString(base_match[4].str());
  }
  m_pf->getCompilationUnit()->recordTimeInfo(compUnitTimeInfo);
}


void SV3_1aTreeShapeListener::enterTimeUnitsDecl_TimePrecision(
    SV3_1aParser::TimeUnitsDecl_TimePrecisionContext *ctx) {
  if (m_currentElement) {
    m_currentElement->m_timeInfo.m_type = TimeInfo::Type::TimeUnitTimePrecision;
    auto pair = getTimeValue(ctx->time_literal());
    m_currentElement->m_timeInfo.m_timePrecisionValue = pair.first;
    m_currentElement->m_timeInfo.m_timePrecision = pair.second;
  }
}

void SV3_1aTreeShapeListener::enterTimeUnitsDecl_TimeUnitTimePrecision(
    SV3_1aParser::TimeUnitsDecl_TimeUnitTimePrecisionContext *ctx) {
  if (m_currentElement) {
    m_currentElement->m_timeInfo.m_type = TimeInfo::Type::TimeUnitTimePrecision;
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
    m_currentElement->m_timeInfo.m_type = TimeInfo::Type::TimeUnitTimePrecision;
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
    m_currentElement->m_timeInfo.m_type = TimeInfo::Type::TimeUnitTimePrecision;
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

void SV3_1aTreeShapeListener::exitInitVal_Integral(
    SV3_1aParser::InitVal_IntegralContext *ctx) {
  auto number = ctx->Integral_number();
  addVObject(ctx, number->getText(),
             VObjectType::slIntConst);  // TODO: Octal, Hexa...
}

void SV3_1aTreeShapeListener::exitScalar_Integral(
    SV3_1aParser::Scalar_IntegralContext *ctx) {
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

void SV3_1aTreeShapeListener::exitPound_delay_value(
  SV3_1aParser::Pound_delay_valueContext *ctx) {
  if (ctx->Pound_delay()) {
     addVObject(ctx, ctx->Pound_delay()->getText(),
             VObjectType::slIntConst);
  } else if (ctx->Pound_Pound_delay()) {
     addVObject(ctx, ctx->Pound_Pound_delay()->getText(),
             VObjectType::slPound_Pound_delay);
  } else if (ctx->delay_value()) {
     addVObject(ctx, ctx->delay_value()->getText(),
             VObjectType::slIntConst);
  }
}

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

  // !!! Don't forget to change CompileModule.cpp type checker !!!
  addVObject(ctx, ident, VObjectType::slStringConst);

  if (ident.size() > SV_MAX_IDENTIFIER_SIZE) {
    logError(ErrorDefinition::PA_MAX_LENGTH_IDENTIFIER, ctx, ident);
  }
}

void SV3_1aTreeShapeListener::exitUnique_priority(SV3_1aParser::Unique_priorityContext * ctx) {
  if (ctx->PRIORITY()) {
    addVObject((ParserRuleContext *)ctx->PRIORITY(), VObjectType::slPriority);
  } else if (ctx->UNIQUE()) {
    addVObject((ParserRuleContext *)ctx->UNIQUE(), VObjectType::slUnique);
  } else if (ctx->UNIQUE0()) {
    addVObject((ParserRuleContext *)ctx->UNIQUE0(), VObjectType::slUnique0);
  }
  addVObject (ctx, VObjectType::slUnique_priority);
}

void SV3_1aTreeShapeListener::exitCase_keyword(SV3_1aParser::Case_keywordContext * ctx) {
  if (ctx->CASE()) {
    addVObject((ParserRuleContext *)ctx->CASE(), VObjectType::slCase);
  } else  if (ctx->CASEX()) {
    addVObject((ParserRuleContext *)ctx->CASEX(), VObjectType::slCaseX);
  } else  if (ctx->CASEZ()) {
    addVObject((ParserRuleContext *)ctx->CASEZ(), VObjectType::slCaseZ);
  }
  addVObject (ctx, VObjectType::slCase_keyword);
}

void SV3_1aTreeShapeListener::exitPart_select_op_column(SV3_1aParser::Part_select_op_columnContext * ctx) {
  if (ctx->INC_PART_SELECT_OP()) {
    addVObject (ctx, VObjectType::slIncPartSelectOp);
  } else  if (ctx->DEC_PART_SELECT_OP()) {
    addVObject(ctx, VObjectType::slDecPartSelectOp);
  } else  if (ctx->COLUMN()) {
    addVObject(ctx, VObjectType::slColumnPartSelectOp);
  }
}

void SV3_1aTreeShapeListener::exitPart_select_op(SV3_1aParser::Part_select_opContext * ctx) {
  if (ctx->INC_PART_SELECT_OP()) {
    addVObject (ctx, VObjectType::slIncPartSelectOp);
  } else  if (ctx->DEC_PART_SELECT_OP()) {
    addVObject(ctx, VObjectType::slDecPartSelectOp);
  }
}

void SV3_1aTreeShapeListener::exitSystem_task_names(SV3_1aParser::System_task_namesContext * ctx) {
  std::string ident = ctx->getText();
  if (ctx->TIME())
    addVObject((ParserRuleContext *)ctx->TIME(), ident, VObjectType::slStringConst);
  else if (ctx->REALTIME())
    addVObject((ParserRuleContext *)ctx->REALTIME(), ident, VObjectType::slStringConst);
  else if (ctx->ASSERT())
    addVObject((ParserRuleContext *)ctx->ASSERT(), ident, VObjectType::slStringConst);
  else if (ctx->Simple_identifier().size())
    addVObject((ParserRuleContext *)ctx->Simple_identifier()[0], ident, VObjectType::slStringConst);
  else if (ctx->SIGNED())
    addVObject((ParserRuleContext *)ctx->SIGNED(), ident, VObjectType::slStringConst);
  else if (ctx->UNSIGNED())
    addVObject((ParserRuleContext *)ctx->UNSIGNED(), ident, VObjectType::slStringConst);
  addVObject(ctx, VObjectType::slSystem_task_names);
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
  if (ctx->dollar_root_keyword()) {
    childCtx = (ParserRuleContext *)ctx->children[1];
    ident = ctx->getText();
  } else {
    childCtx = (ParserRuleContext *)ctx->children[0];
    ident = ctx->getText();
  }
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

void SV3_1aTreeShapeListener::exitAnonymous_program(SV3_1aParser::Anonymous_programContext * ctx)  {
  if (ctx->ENDPROGRAM())
    addVObject ((ParserRuleContext*)ctx->ENDPROGRAM(), VObjectType::slEndprogram);
  addVObject (ctx, VObjectType::slAnonymous_program);
}

void SV3_1aTreeShapeListener::exitProgram_declaration(SV3_1aParser::Program_declarationContext * ctx) {
  if (ctx->ENDPROGRAM())
    addVObject ((ParserRuleContext*)ctx->ENDPROGRAM(), VObjectType::slEndprogram);
  addVObject (ctx, VObjectType::slProgram_declaration);
}

void SV3_1aTreeShapeListener::exitProcedural_continuous_assignment(SV3_1aParser::Procedural_continuous_assignmentContext * ctx) {
  if (ctx->ASSIGN()) {
    addVObject ((ParserRuleContext*)ctx->ASSIGN(), VObjectType::slAssign);
  } else if (ctx->DEASSIGN()) {
    addVObject ((ParserRuleContext*)ctx->DEASSIGN(), VObjectType::slDeassign);
  } else if (ctx->FORCE()) {
    addVObject ((ParserRuleContext*)ctx->FORCE(), VObjectType::slForce);
  } else if (ctx->RELEASE()) {
    addVObject ((ParserRuleContext*)ctx->RELEASE(), VObjectType::slRelease);
  }
  addVObject (ctx, VObjectType::slProcedural_continuous_assignment);
}

void SV3_1aTreeShapeListener::exitDrive_strength(SV3_1aParser::Drive_strengthContext * ctx)  {
  if (ctx->SUPPLY0()) {
    addVObject ((ParserRuleContext*)ctx->SUPPLY0(), VObjectType::slSupply0);
  } else if (ctx->STRONG0()) {
    addVObject ((ParserRuleContext*)ctx->STRONG0(), VObjectType::slStrong0);
  } else if (ctx->PULL0()) {
    addVObject ((ParserRuleContext*)ctx->PULL0(), VObjectType::slPull0);
  } else if (ctx->WEAK0()) {
    addVObject ((ParserRuleContext*)ctx->WEAK0(), VObjectType::slWeak0);
  }
  if (ctx->SUPPLY1()) {
    addVObject ((ParserRuleContext*)ctx->SUPPLY1(), VObjectType::slSupply1);
  } else if (ctx->STRONG1()) {
    addVObject ((ParserRuleContext*)ctx->STRONG1(), VObjectType::slStrong1);
  } else if (ctx->PULL1()) {
    addVObject ((ParserRuleContext*)ctx->PULL1(), VObjectType::slPull1);
  } else if (ctx->WEAK1()) {
    addVObject ((ParserRuleContext*)ctx->WEAK1(), VObjectType::slWeak1);
  }

  if (ctx->HIGHZ0()) {
    addVObject ((ParserRuleContext*)ctx->HIGHZ0(), VObjectType::slHighZ0);
  } else if (ctx->HIGHZ1()) {
    addVObject ((ParserRuleContext*)ctx->HIGHZ1(), VObjectType::slHighZ1);
  }
  addVObject (ctx, VObjectType::slDrive_strength);
}

void SV3_1aTreeShapeListener::exitStrength0(SV3_1aParser::Strength0Context * ctx)  {
  if (ctx->SUPPLY0()) {
    addVObject ((ParserRuleContext*)ctx->SUPPLY0(), VObjectType::slSupply0);
  } else if (ctx->STRONG0()) {
    addVObject ((ParserRuleContext*)ctx->STRONG0(), VObjectType::slStrong0);
  } else if (ctx->PULL0()) {
    addVObject ((ParserRuleContext*)ctx->PULL0(), VObjectType::slPull0);
  } else if (ctx->WEAK0()) {
    addVObject ((ParserRuleContext*)ctx->WEAK0(), VObjectType::slWeak0);
  }
  addVObject (ctx, VObjectType::slStrength0);
}

void SV3_1aTreeShapeListener::exitAction_block(SV3_1aParser::Action_blockContext * ctx)
{
  if (ctx->ELSE()) {
    addVObject ((ParserRuleContext*)ctx->ELSE(), VObjectType::slElse);
  }
  addVObject (ctx, VObjectType::slAction_block);
}

void SV3_1aTreeShapeListener::exitEvent_trigger(SV3_1aParser::Event_triggerContext * ctx)
{
  if (ctx->IMPLY())
    addVObject ((ParserRuleContext*)ctx->IMPLY(), VObjectType::slBinOp_Imply);
  if (ctx->NON_BLOCKING_TRIGGER_EVENT_OP())
    addVObject ((ParserRuleContext*)ctx->NON_BLOCKING_TRIGGER_EVENT_OP(), VObjectType::slNonBlockingTriggerEvent);
  addVObject (ctx, VObjectType::slEvent_trigger);
}


void SV3_1aTreeShapeListener::exitStrength1(SV3_1aParser::Strength1Context * ctx)  {
  if (ctx->SUPPLY1()) {
    addVObject ((ParserRuleContext*)ctx->SUPPLY1(), VObjectType::slSupply1);
  } else if (ctx->STRONG1()) {
    addVObject ((ParserRuleContext*)ctx->STRONG1(), VObjectType::slStrong1);
  } else if (ctx->PULL1()) {
    addVObject ((ParserRuleContext*)ctx->PULL1(), VObjectType::slPull1);
  } else if (ctx->WEAK1()) {
    addVObject ((ParserRuleContext*)ctx->WEAK1(), VObjectType::slWeak1);
  }
  addVObject (ctx, VObjectType::slStrength1);
}

void SV3_1aTreeShapeListener::exitCharge_strength(SV3_1aParser::Charge_strengthContext * ctx) {
  if (ctx->SMALL()) {
    addVObject ((ParserRuleContext*)ctx->SMALL(), VObjectType::slSmall);
  } else if (ctx->MEDIUM()) {
    addVObject ((ParserRuleContext*)ctx->MEDIUM(), VObjectType::slMedium);
  } else if (ctx->LARGE()) {
    addVObject ((ParserRuleContext*)ctx->LARGE(), VObjectType::slLarge);
  }
  addVObject (ctx, VObjectType::slCharge_strength);
}

void SV3_1aTreeShapeListener::exitStream_operator(SV3_1aParser::Stream_operatorContext * ctx) {
  if (ctx->SHIFT_RIGHT()) {
    addVObject ((ParserRuleContext*)ctx->SHIFT_RIGHT(), VObjectType::slBinOp_ShiftRight);
  } else if (ctx->SHIFT_LEFT()) {
    addVObject ((ParserRuleContext*)ctx->SHIFT_LEFT(), VObjectType::slBinOp_ShiftLeft);
  }
  addVObject (ctx, VObjectType::slStream_operator);
}

void SV3_1aTreeShapeListener::exitLoop_statement(SV3_1aParser::Loop_statementContext * ctx) {
  if (ctx->DO()) {
    addVObject ((ParserRuleContext*)ctx->DO(), VObjectType::slDo);
  } else if (ctx->FOREVER()) {
    addVObject ((ParserRuleContext*)ctx->FOREVER(), VObjectType::slForever);
  } else if (ctx->REPEAT()) {
    addVObject ((ParserRuleContext*)ctx->REPEAT(), VObjectType::slRepeat);
  } else if (ctx->WHILE()) {
    addVObject ((ParserRuleContext*)ctx->WHILE(), VObjectType::slWhile);
  } else if (ctx->FOR()) {
    addVObject ((ParserRuleContext*)ctx->FOR(), VObjectType::slFor);
  } else if (ctx->FOREACH()) {
    addVObject ((ParserRuleContext*)ctx->FOREACH(), VObjectType::slForeach);
  }
  addVObject (ctx, VObjectType::slLoop_statement);
}


void SV3_1aTreeShapeListener::exitPackage_scope(
    SV3_1aParser::Package_scopeContext *ctx) {
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
  addVObject(ctx, VObjectType::slPackage_scope);

  if (ident.size() > SV_MAX_IDENTIFIER_SIZE) {
    logError(ErrorDefinition::PA_MAX_LENGTH_IDENTIFIER, ctx, ident);
  }
}

void SV3_1aTreeShapeListener::exitExpression(SV3_1aParser::ExpressionContext * ctx) {
  if (ctx->MATCHES()) {
    addVObject ((ParserRuleContext*)ctx->MATCHES(), VObjectType::slMatches);
  } 
  if (ctx->PLUS()) {
    if (ctx->expression().size() == 1)
      addVObject ((ParserRuleContext*)ctx->PLUS(), VObjectType::slUnary_Plus);
    else
      addVObject ((ParserRuleContext*)ctx->PLUS(), VObjectType::slBinOp_Plus);
  } else if (ctx->MINUS()) {
    if (ctx->expression().size() == 1)
      addVObject ((ParserRuleContext*)ctx->MINUS(), VObjectType::slUnary_Minus);
    else
      addVObject ((ParserRuleContext*)ctx->MINUS(), VObjectType::slBinOp_Minus);
  } else if (ctx->BANG()) {
    addVObject ((ParserRuleContext*)ctx->BANG(), VObjectType::slUnary_Not);
  } else if (ctx->TILDA()) {
    addVObject ((ParserRuleContext*)ctx->TILDA(), VObjectType::slUnary_Tilda);
  } else if (ctx->BITW_AND()) {
    if (ctx->expression().size() == 1)
      addVObject ((ParserRuleContext*)ctx->BITW_AND(), VObjectType::slUnary_BitwAnd);
    else
      addVObject ((ParserRuleContext*)ctx->BITW_AND(), VObjectType::slBinOp_BitwAnd);
  } else if (ctx->BITW_OR()) {
    if (ctx->expression().size() == 1)
      addVObject ((ParserRuleContext*)ctx->BITW_OR(), VObjectType::slUnary_BitwOr);
    else
      addVObject ((ParserRuleContext*)ctx->BITW_OR(), VObjectType::slBinOp_BitwOr);
  } else if (ctx->BITW_XOR()) {
    if (ctx->expression().size() == 1)
      addVObject ((ParserRuleContext*)ctx->BITW_XOR(), VObjectType::slUnary_BitwXor);
    else
      addVObject ((ParserRuleContext*)ctx->BITW_XOR(), VObjectType::slBinOp_BitwXor); 
  } else if (ctx->REDUCTION_NAND()) {
    if (ctx->expression().size() == 1)
      addVObject ((ParserRuleContext*)ctx->REDUCTION_NAND(), VObjectType::slUnary_ReductNand);
    else
      addVObject ((ParserRuleContext*)ctx->REDUCTION_NAND(), VObjectType::slBinOp_ReductNand);
  } else if (ctx->REDUCTION_NOR()) {
    addVObject ((ParserRuleContext*)ctx->REDUCTION_NOR(), VObjectType::slUnary_ReductNor);
  } else if (ctx->REDUCTION_XNOR1()) {
    if (ctx->expression().size() == 1)
      addVObject ((ParserRuleContext*)ctx->REDUCTION_XNOR1(), VObjectType::slUnary_ReductXnor1);
    else
      addVObject ((ParserRuleContext*)ctx->REDUCTION_XNOR1(), VObjectType::slBinOp_ReductXnor1);
  } else if (ctx->REDUCTION_XNOR2()) {
    if (ctx->expression().size() == 1)
      addVObject ((ParserRuleContext*)ctx->REDUCTION_XNOR2(), VObjectType::slUnary_ReductXnor2);
    else
      addVObject ((ParserRuleContext*)ctx->REDUCTION_XNOR2(), VObjectType::slBinOp_ReductXnor2);
  } else if (ctx->STARSTAR()) {
    addVObject ((ParserRuleContext*)ctx->STARSTAR(), VObjectType::slBinOp_MultMult);
  } else if (ctx->STAR()) {
    addVObject ((ParserRuleContext*)ctx->STAR(), VObjectType::slBinOp_Mult);
  } else if (ctx->DIV()) {
    addVObject ((ParserRuleContext*)ctx->DIV(), VObjectType::slBinOp_Div);
  } else if (ctx->PERCENT()) {
    addVObject ((ParserRuleContext*)ctx->PERCENT(), VObjectType::slBinOp_Percent);
  } else if (ctx->SHIFT_RIGHT()) {
    addVObject ((ParserRuleContext*)ctx->SHIFT_RIGHT(), VObjectType::slBinOp_ShiftRight);
  } else if (ctx->SHIFT_LEFT()) {
    addVObject ((ParserRuleContext*)ctx->SHIFT_LEFT(), VObjectType::slBinOp_ShiftLeft);
  } else if (ctx->ARITH_SHIFT_RIGHT()) {
    addVObject ((ParserRuleContext*)ctx->ARITH_SHIFT_RIGHT(), VObjectType::slBinOp_ArithShiftRight);
  } else if (ctx->ARITH_SHIFT_LEFT()) {
    addVObject ((ParserRuleContext*)ctx->ARITH_SHIFT_LEFT(), VObjectType::slBinOp_ArithShiftLeft);
  } else if (ctx->LESS()) {
    addVObject ((ParserRuleContext*)ctx->LESS(), VObjectType::slBinOp_Less);
  } else if (ctx->LESS_EQUAL()) {
    addVObject ((ParserRuleContext*)ctx->LESS_EQUAL(), VObjectType::slBinOp_LessEqual);
  } else if (ctx->PLUSPLUS()) {
    addVObject ((ParserRuleContext*)ctx->PLUSPLUS(), VObjectType::slIncDec_PlusPlus);
  }  else if (ctx->MINUSMINUS()) {
    addVObject ((ParserRuleContext*)ctx->MINUSMINUS(), VObjectType::slIncDec_MinusMinus);
  } else if (ctx->GREATER()) {
    addVObject ((ParserRuleContext*)ctx->GREATER(), VObjectType::slBinOp_Great);
  } else if (ctx->GREATER_EQUAL()) {
    addVObject ((ParserRuleContext*)ctx->GREATER_EQUAL(), VObjectType::slBinOp_GreatEqual);
  } else if (ctx->INSIDE()) {
    addVObject ((ParserRuleContext*)ctx->INSIDE(), VObjectType::slInsideOp);
  } else if (ctx->EQUIV()) {
    addVObject ((ParserRuleContext*)ctx->EQUIV(), VObjectType::slBinOp_Equiv);
  } else if (ctx->NOTEQUAL()) {
    addVObject ((ParserRuleContext*)ctx->NOTEQUAL(), VObjectType::slBinOp_Not);
  } else if (ctx->BINARY_WILDCARD_EQUAL()) {
    addVObject ((ParserRuleContext*)ctx->BINARY_WILDCARD_EQUAL(), VObjectType::slBinOp_WildcardEqual);
  } else if (ctx->BINARY_WILDCARD_NOTEQUAL()) {
    addVObject ((ParserRuleContext*)ctx->BINARY_WILDCARD_NOTEQUAL(), VObjectType::slBinOp_WildcardNotEqual);
  } else if (ctx->FOUR_STATE_LOGIC_EQUAL()) {
    addVObject ((ParserRuleContext*)ctx->FOUR_STATE_LOGIC_EQUAL(), VObjectType::slBinOp_FourStateLogicEqual);
  } else if (ctx->FOUR_STATE_LOGIC_NOTEQUAL()) {
    addVObject ((ParserRuleContext*)ctx->FOUR_STATE_LOGIC_NOTEQUAL(), VObjectType::slBinOp_FourStateLogicNotEqual);
  } else if (ctx->WILD_EQUAL_OP()) {
    addVObject ((ParserRuleContext*)ctx->WILD_EQUAL_OP(), VObjectType::slBinOp_WildEqual);
  } else if (ctx->WILD_NOTEQUAL_OP()) {
    addVObject ((ParserRuleContext*)ctx->WILD_NOTEQUAL_OP(), VObjectType::slBinOp_WildEqual);
  } else if (ctx->BITW_AND()) {
    if (ctx->expression().size() == 1)
      addVObject ((ParserRuleContext*)ctx->BITW_AND(), VObjectType::slUnary_BitwAnd);
    else
      addVObject ((ParserRuleContext*)ctx->BITW_AND(), VObjectType::slBinOp_BitwAnd);
  } else if (ctx->LOGICAL_AND().size()) {
    addVObject ((ParserRuleContext*)ctx->LOGICAL_AND()[0], VObjectType::slBinOp_LogicAnd);
  } else if (ctx->LOGICAL_OR()) {
    addVObject ((ParserRuleContext*)ctx->LOGICAL_OR(), VObjectType::slBinOp_LogicOr);
  } else if (ctx->IMPLY()) {
    addVObject ((ParserRuleContext*)ctx->IMPLY(), VObjectType::slBinOp_Imply);
  } else if (ctx->EQUIVALENCE()) {
    addVObject ((ParserRuleContext*)ctx->EQUIVALENCE(), VObjectType::slBinOp_Equivalence);
  } else if (ctx->TAGGED()) {
    addVObject ((ParserRuleContext*)ctx->TAGGED(), VObjectType::slTagged);
  } 
  if (ctx->QMARK()) {
    addVObject ((ParserRuleContext*)ctx->QMARK(), VObjectType::slQmark);
  } 
  addVObject (ctx, VObjectType::slExpression);
}

void SV3_1aTreeShapeListener::exitEvent_expression(SV3_1aParser::Event_expressionContext * ctx) {
  if (ctx->IFF()) {
      addVObject ((ParserRuleContext*)ctx->IFF(), VObjectType::slIff);
  }
  addVObject (ctx, VObjectType::slEvent_expression);
}

void SV3_1aTreeShapeListener::exitConstant_expression(SV3_1aParser::Constant_expressionContext * ctx) {
  if (ctx->PLUS()) {
    if (ctx->constant_primary())
      addVObject ((ParserRuleContext*)ctx->PLUS(), VObjectType::slUnary_Plus);
    else
      addVObject ((ParserRuleContext*)ctx->PLUS(), VObjectType::slBinOp_Plus);
  } else if (ctx->MINUS()) {
    if (ctx->constant_primary())
      addVObject ((ParserRuleContext*)ctx->MINUS(), VObjectType::slUnary_Minus);
    else
      addVObject ((ParserRuleContext*)ctx->MINUS(), VObjectType::slBinOp_Minus);
  } else if (ctx->BANG()) {
    addVObject ((ParserRuleContext*)ctx->BANG(), VObjectType::slUnary_Not);
  } else if (ctx->TILDA()) {
    addVObject ((ParserRuleContext*)ctx->TILDA(), VObjectType::slUnary_Tilda);
  } else if (ctx->BITW_AND()) {
    if (ctx->constant_primary())
      addVObject ((ParserRuleContext*)ctx->BITW_AND(), VObjectType::slUnary_BitwAnd);
    else
      addVObject ((ParserRuleContext*)ctx->BITW_AND(), VObjectType::slBinOp_BitwAnd);
  } else if (ctx->BITW_OR()) {
    if (ctx->constant_primary())
      addVObject ((ParserRuleContext*)ctx->BITW_OR(), VObjectType::slUnary_BitwOr);
    else
      addVObject ((ParserRuleContext*)ctx->BITW_OR(), VObjectType::slBinOp_BitwOr);
  } else if (ctx->BITW_XOR()) {
    if (ctx->constant_primary())
      addVObject ((ParserRuleContext*)ctx->BITW_XOR(), VObjectType::slUnary_BitwXor);
    else
      addVObject ((ParserRuleContext*)ctx->BITW_XOR(), VObjectType::slBinOp_BitwXor); 
  } else if (ctx->REDUCTION_NAND()) {
    if (ctx->constant_primary())
      addVObject ((ParserRuleContext*)ctx->REDUCTION_NAND(), VObjectType::slUnary_ReductNand);
    else
      addVObject ((ParserRuleContext*)ctx->REDUCTION_NAND(), VObjectType::slBinOp_ReductNand);
  } else if (ctx->REDUCTION_NOR()) {
    addVObject ((ParserRuleContext*)ctx->REDUCTION_NOR(), VObjectType::slUnary_ReductNor);
  } else if (ctx->REDUCTION_XNOR1()) {
    if (ctx->constant_primary())
      addVObject ((ParserRuleContext*)ctx->REDUCTION_XNOR1(), VObjectType::slUnary_ReductXnor1);
    else
      addVObject ((ParserRuleContext*)ctx->REDUCTION_XNOR1(), VObjectType::slBinOp_ReductXnor1);
  } else if (ctx->REDUCTION_XNOR2()) {
    if (ctx->constant_primary())
      addVObject ((ParserRuleContext*)ctx->REDUCTION_XNOR2(), VObjectType::slUnary_ReductXnor2);
    else
      addVObject ((ParserRuleContext*)ctx->REDUCTION_XNOR2(), VObjectType::slBinOp_ReductXnor2);
  } else if (ctx->STARSTAR()) {
    addVObject ((ParserRuleContext*)ctx->STARSTAR(), VObjectType::slBinOp_MultMult);
  } else if (ctx->STAR()) {
    addVObject ((ParserRuleContext*)ctx->STAR(), VObjectType::slBinOp_Mult);
  } else if (ctx->DIV()) {
    addVObject ((ParserRuleContext*)ctx->DIV(), VObjectType::slBinOp_Div);
  } else if (ctx->PERCENT()) {
    addVObject ((ParserRuleContext*)ctx->PERCENT(), VObjectType::slBinOp_Percent);
  } else if (ctx->SHIFT_RIGHT()) {
    addVObject ((ParserRuleContext*)ctx->SHIFT_RIGHT(), VObjectType::slBinOp_ShiftRight);
  } else if (ctx->SHIFT_LEFT()) {
    addVObject ((ParserRuleContext*)ctx->SHIFT_LEFT(), VObjectType::slBinOp_ShiftLeft);
  } else if (ctx->ARITH_SHIFT_RIGHT()) {
    addVObject ((ParserRuleContext*)ctx->ARITH_SHIFT_RIGHT(), VObjectType::slBinOp_ArithShiftRight);
  } else if (ctx->ARITH_SHIFT_LEFT()) {
    addVObject ((ParserRuleContext*)ctx->ARITH_SHIFT_LEFT(), VObjectType::slBinOp_ArithShiftLeft);
  } else if (ctx->LESS()) {
    addVObject ((ParserRuleContext*)ctx->LESS(), VObjectType::slBinOp_Less);
  } else if (ctx->LESS_EQUAL()) {
    addVObject ((ParserRuleContext*)ctx->LESS_EQUAL(), VObjectType::slBinOp_LessEqual);
  } else if (ctx->GREATER()) {
    addVObject ((ParserRuleContext*)ctx->GREATER(), VObjectType::slBinOp_Great);
  } else if (ctx->GREATER_EQUAL()) {
    addVObject ((ParserRuleContext*)ctx->GREATER_EQUAL(), VObjectType::slBinOp_GreatEqual);
  } else if (ctx->INSIDE()) {
    addVObject ((ParserRuleContext*)ctx->INSIDE(), VObjectType::slInsideOp);
  } else if (ctx->EQUIV()) {
    addVObject ((ParserRuleContext*)ctx->EQUIV(), VObjectType::slBinOp_Equiv);
  } else if (ctx->NOTEQUAL()) {
    addVObject ((ParserRuleContext*)ctx->NOTEQUAL(), VObjectType::slBinOp_Not);
  } else if (ctx->BINARY_WILDCARD_EQUAL()) {
    addVObject ((ParserRuleContext*)ctx->BINARY_WILDCARD_EQUAL(), VObjectType::slBinOp_WildcardEqual);
  } else if (ctx->BINARY_WILDCARD_NOTEQUAL()) {
    addVObject ((ParserRuleContext*)ctx->BINARY_WILDCARD_NOTEQUAL(), VObjectType::slBinOp_WildcardNotEqual);
  } else if (ctx->FOUR_STATE_LOGIC_EQUAL()) {
    addVObject ((ParserRuleContext*)ctx->FOUR_STATE_LOGIC_EQUAL(), VObjectType::slBinOp_FourStateLogicEqual);
  } else if (ctx->FOUR_STATE_LOGIC_NOTEQUAL()) {
    addVObject ((ParserRuleContext*)ctx->FOUR_STATE_LOGIC_NOTEQUAL(), VObjectType::slBinOp_FourStateLogicNotEqual);
  } else if (ctx->WILD_EQUAL_OP()) {
    addVObject ((ParserRuleContext*)ctx->WILD_EQUAL_OP(), VObjectType::slBinOp_WildEqual);
  } else if (ctx->WILD_NOTEQUAL_OP()) {
    addVObject ((ParserRuleContext*)ctx->WILD_NOTEQUAL_OP(), VObjectType::slBinOp_WildEqual);
  } else if (ctx->BITW_AND()) {
    if (ctx->constant_primary())
      addVObject ((ParserRuleContext*)ctx->BITW_AND(), VObjectType::slUnary_BitwAnd);
    else
      addVObject ((ParserRuleContext*)ctx->BITW_AND(), VObjectType::slBinOp_BitwAnd);
  } else if (ctx->LOGICAL_AND().size()) {
    addVObject ((ParserRuleContext*)ctx->LOGICAL_AND()[0], VObjectType::slBinOp_LogicAnd);
  } else if (ctx->LOGICAL_OR()) {
    addVObject ((ParserRuleContext*)ctx->LOGICAL_OR(), VObjectType::slBinOp_LogicOr);
  } else if (ctx->IMPLY()) {
    addVObject ((ParserRuleContext*)ctx->IMPLY(), VObjectType::slBinOp_Imply);
  } else if (ctx->EQUIVALENCE()) {
    addVObject ((ParserRuleContext*)ctx->EQUIVALENCE(), VObjectType::slBinOp_Equivalence);
  } 
  addVObject (ctx, VObjectType::slConstant_expression);
}

void  SV3_1aTreeShapeListener::exitNet_type(SV3_1aParser::Net_typeContext * ctx) {
  if (ctx->SUPPLY0()) {
    addVObject (ctx, VObjectType::slNetType_Supply0);
  } else if (ctx->SUPPLY1()) {
    addVObject (ctx, VObjectType::slNetType_Supply1);
  } else if (ctx->TRI()) {
    addVObject (ctx, VObjectType::slNetType_Tri);
  } else if (ctx->TRIAND()) {
    addVObject (ctx, VObjectType::slNetType_TriAnd);  
  } else if (ctx->TRIOR()) {
    addVObject (ctx, VObjectType::slNetType_TriOr);  
  } else if (ctx->TRIREG()) {
    addVObject (ctx, VObjectType::slNetType_TriReg); 
  } else if (ctx->TRI0()) {
    addVObject (ctx, VObjectType::slNetType_Tri0);    
  } else if (ctx->TRI1()) {
    addVObject (ctx, VObjectType::slNetType_Tri1);  
  } else if (ctx->UWIRE()) {
    addVObject (ctx, VObjectType::slNetType_Uwire); 
  } else if (ctx->WIRE()) {
    addVObject (ctx, VObjectType::slNetType_Wire);  
  } else if (ctx->WAND()) {
    addVObject (ctx, VObjectType::slNetType_Wand); 
  } else if (ctx->WOR()) {
    addVObject (ctx, VObjectType::slNetType_Wor);
  }
}

void SV3_1aTreeShapeListener::exitAssignment_operator(SV3_1aParser::Assignment_operatorContext * ctx) {
  if (ctx->ASSIGN_OP()) {
    addVObject (ctx, VObjectType::slAssignOp_Assign);
  } else if (ctx->ADD_ASSIGN()) {
    addVObject (ctx, VObjectType::slAssignOp_Add);
  } else if (ctx->SUB_ASSIGN()) {
    addVObject (ctx, VObjectType::slAssignOp_Sub);
  } else if (ctx->MULT_ASSIGN()) {
    addVObject (ctx, VObjectType::slAssignOp_Mult);
  } else if (ctx->DIV_ASSIGN()) {
    addVObject (ctx, VObjectType::slAssignOp_Div);
  } else if (ctx->MODULO_ASSIGN()) {
    addVObject (ctx, VObjectType::slAssignOp_Modulo);
  } else if (ctx->BITW_AND_ASSIGN()) {
    addVObject (ctx, VObjectType::slAssignOp_BitwAnd);
  } else if (ctx->BITW_OR_ASSIGN()) {
    addVObject (ctx, VObjectType::slAssignOp_BitwOr);
  } else if (ctx->BITW_XOR_ASSIGN()) {
    addVObject (ctx, VObjectType::slAssignOp_BitwXor);
  } else if (ctx->BITW_LEFT_SHIFT_ASSIGN()) {
    addVObject (ctx, VObjectType::slAssignOp_BitwLeftShift);
  } else if (ctx->BITW_RIGHT_SHIFT_ASSIGN()) {
    addVObject (ctx, VObjectType::slAssignOp_BitwRightShift);
  } else if (ctx->ARITH_SHIFT_LEFT_ASSIGN()) {
    addVObject (ctx, VObjectType::slAssignOp_ArithShiftLeft);
  } else if (ctx->ARITH_SHIFT_RIGHT_ASSIGN()) {
    addVObject (ctx, VObjectType::slAssignOp_ArithShiftRight);
  }   
}

void SV3_1aTreeShapeListener::exitInc_or_dec_operator(SV3_1aParser::Inc_or_dec_operatorContext* ctx)  {
  if (ctx->PLUSPLUS()) 
    addVObject (ctx, VObjectType::slIncDec_PlusPlus);
  else 
    addVObject (ctx, VObjectType::slIncDec_MinusMinus);
}

void SV3_1aTreeShapeListener::exitGate_instantiation(SV3_1aParser::Gate_instantiationContext * ctx) {
  if (ctx->PULLUP()) {
    addVObject ((ParserRuleContext*)ctx->PULLUP(), VObjectType::slPullup);
  } else if (ctx->PULLDOWN()) {
    addVObject ((ParserRuleContext*)ctx->PULLDOWN(), VObjectType::slPulldown);
  }
  addVObject (ctx, VObjectType::slGate_instantiation);
}

void SV3_1aTreeShapeListener::exitOutput_symbol(SV3_1aParser::Output_symbolContext * ctx) {
  if (ctx->Integral_number()) {
    auto number = ctx->Integral_number();
    addVObject((ParserRuleContext*)ctx->Integral_number(), number->getText(), VObjectType::slIntConst);
  } else if (ctx->Simple_identifier()) {
    std::string ident = ctx->Simple_identifier()->getText();
    addVObject((ParserRuleContext*)ctx->Simple_identifier(), ident, VObjectType::slStringConst);
  }
  addVObject (ctx, VObjectType::slOutput_symbol);
}

void SV3_1aTreeShapeListener::exitCycle_delay(SV3_1aParser::Cycle_delayContext * ctx) {
  if (ctx->Integral_number()) {
    auto number = ctx->Integral_number();
    addVObject((ParserRuleContext*)ctx->Integral_number(), number->getText(), VObjectType::slIntConst);
  }
  if (ctx->Pound_Pound_delay()) {
    addVObject ((ParserRuleContext*)ctx->Pound_Pound_delay(), ctx->Pound_Pound_delay()->getText(), VObjectType::slPound_Pound_delay);
  }
  addVObject (ctx, VObjectType::slCycle_delay);
}

void SV3_1aTreeShapeListener::exitCycle_delay_range(SV3_1aParser::Cycle_delay_rangeContext * ctx) {
  if (ctx->Pound_Pound_delay()) {
    addVObject ((ParserRuleContext*)ctx->Pound_Pound_delay(), ctx->Pound_Pound_delay()->getText(), VObjectType::slPound_Pound_delay);
  }
  if (ctx->PLUS()) {
    addVObject ((ParserRuleContext*)ctx->PLUS(), VObjectType::slUnary_Plus);
  }
  addVObject (ctx, VObjectType::slCycle_delay_range);
}
 

void SV3_1aTreeShapeListener::exitLevel_symbol(SV3_1aParser::Level_symbolContext * ctx) {
  if (ctx->Integral_number()) {
    auto number = ctx->Integral_number();
    addVObject((ParserRuleContext*)ctx->Integral_number(), number->getText(), VObjectType::slIntConst);
  } else if (ctx->Simple_identifier()) {
    std::string ident = ctx->Simple_identifier()->getText();
    addVObject((ParserRuleContext*)ctx->Simple_identifier(), ident, VObjectType::slStringConst);
  } else if (ctx->QMARK()) {
    addVObject ((ParserRuleContext*)ctx->QMARK(), VObjectType::slQmark);
  }
  addVObject (ctx, VObjectType::slLevel_symbol);
}

void SV3_1aTreeShapeListener::exitEdge_symbol(SV3_1aParser::Edge_symbolContext * ctx) {
  if (ctx->Simple_identifier()) {
    std::string ident = ctx->Simple_identifier()->getText();
    addVObject((ParserRuleContext*)ctx->Simple_identifier(), ident, VObjectType::slStringConst);
  } else if (ctx->STAR()) {
    addVObject ((ParserRuleContext*)ctx->STAR(), VObjectType::slBinOp_Mult);
  }
  addVObject (ctx, VObjectType::slEdge_symbol);
}

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
}

void SV3_1aTreeShapeListener::exitEnd_keywords_directive(
    SV3_1aParser::End_keywords_directiveContext *ctx) {
}

void SV3_1aTreeShapeListener::exitRandomize_call(SV3_1aParser::Randomize_callContext * ctx) {
  if (ctx->NULL_KEYWORD()) {
    addVObject ((ParserRuleContext*)ctx->NULL_KEYWORD(), VObjectType::slNull);
  }
  if (ctx->WITH()) {
    addVObject ((ParserRuleContext*)ctx->WITH(), VObjectType::slWith);
  }
  addVObject (ctx, VObjectType::slRandomize_call);
}

void SV3_1aTreeShapeListener::exitDeferred_immediate_assert_statement(SV3_1aParser::Deferred_immediate_assert_statementContext * ctx) {
  if (ctx->Pound_delay()) {
    addVObject ((ParserRuleContext*)ctx->Pound_delay(), ctx->Pound_delay()->getText(), VObjectType::slPound_delay);
  } else if (ctx->Pound_Pound_delay()) {
    addVObject ((ParserRuleContext*)ctx->Pound_Pound_delay(), ctx->Pound_Pound_delay()->getText(), VObjectType::slPound_Pound_delay);
  } 
  addVObject (ctx, VObjectType::slDeferred_immediate_assert_statement);
}

void SV3_1aTreeShapeListener::exitDeferred_immediate_assume_statement(SV3_1aParser::Deferred_immediate_assume_statementContext * ctx) {
  if (ctx->Pound_delay()) {
    addVObject ((ParserRuleContext*)ctx->Pound_delay(), ctx->Pound_delay()->getText(), VObjectType::slPound_delay);
  } else if (ctx->Pound_Pound_delay()) {
    addVObject ((ParserRuleContext*)ctx->Pound_Pound_delay(), ctx->Pound_Pound_delay()->getText(), VObjectType::slPound_Pound_delay);
  } 
  addVObject (ctx, VObjectType::slDeferred_immediate_assume_statement);
}

void SV3_1aTreeShapeListener::exitDeferred_immediate_cover_statement(SV3_1aParser::Deferred_immediate_cover_statementContext * ctx) {
  if (ctx->Pound_delay()) {
    addVObject ((ParserRuleContext*)ctx->Pound_delay(), ctx->Pound_delay()->getText(), VObjectType::slPound_delay);
  } else if (ctx->Pound_Pound_delay()) {
    addVObject ((ParserRuleContext*)ctx->Pound_Pound_delay(), ctx->Pound_Pound_delay()->getText(), VObjectType::slPound_Pound_delay);
  } 
  addVObject (ctx, VObjectType::slDeferred_immediate_cover_statement);
}

void SV3_1aTreeShapeListener::exitLocal_parameter_declaration(SV3_1aParser::Local_parameter_declarationContext * ctx)  {
  if (ctx->TYPE()) {
    addVObject ((ParserRuleContext*)ctx->TYPE(), VObjectType::slType); 
  }
  addVObject (ctx, VObjectType::slLocal_parameter_declaration); 
}
  
void SV3_1aTreeShapeListener::exitParameter_declaration(SV3_1aParser::Parameter_declarationContext * ctx) { 
  if (ctx->TYPE()) {
    addVObject ((ParserRuleContext*)ctx->TYPE(), VObjectType::slType); 
  }
  addVObject (ctx, VObjectType::slParameter_declaration); 
}
