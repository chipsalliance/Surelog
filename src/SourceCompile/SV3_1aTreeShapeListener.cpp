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
#include "SourceCompile/SV3_1aTreeShapeListener.h"

#include <cstdlib>
#include <iostream>
#include <regex>

#include "CommandLine/CommandLineParser.h"
#include "ErrorReporting/ErrorContainer.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/Compiler.h"
#include "SourceCompile/ParseFile.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/SV3_1aPpTreeShapeListener.h"
#include "SourceCompile/SV3_1aTreeShapeHelper.h"
#include "SourceCompile/SymbolTable.h"
#include "Utils/FileUtils.h"
#include "Utils/ParseUtils.h"
#include "Utils/StringUtils.h"
#include "antlr4-runtime.h"
#include "parser/SV3_1aLexer.h"
#include "parser/SV3_1aParser.h"
#include "parser/SV3_1aParserBaseListener.h"

namespace SURELOG {
void SV3_1aTreeShapeListener::enterTop_level_rule(
    SV3_1aParser::Top_level_ruleContext * /*ctx*/) {
  if (m_pf->getFileContent() == nullptr) {
    m_fileContent = new FileContent(
        m_pf->getFileId(0), m_pf->getLibrary(),
        m_pf->getCompileSourceFile()->getSymbolTable(),
        m_pf->getCompileSourceFile()->getErrorContainer(), nullptr, 0);
    m_pf->setFileContent(m_fileContent);
    m_pf->getCompileSourceFile()->getCompiler()->getDesign()->addFileContent(
        m_pf->getFileId(0), m_fileContent);
  } else {
    m_fileContent = m_pf->getFileContent();
  }
  CommandLineParser *clp = m_pf->getCompileSourceFile()->getCommandLineParser();
  if ((!clp->parseOnly()) && (!clp->lowMem())) {
    IncludeFileInfo info(1, m_pf->getFileId(0), 0, IncludeFileInfo::PUSH);
    m_includeFileInfo.push(info);
  }
}

void SV3_1aTreeShapeListener::enterTop_level_library_rule(
    SV3_1aParser::Top_level_library_ruleContext * /*ctx*/) {
  // Visited from Library/SVLibShapeListener.h
  m_fileContent = new FileContent(m_pf->getFileId(0), m_pf->getLibrary(),
                                  m_pf->getSymbolTable(),
                                  m_pf->getErrorContainer(), nullptr, 0);
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

void SV3_1aTreeShapeListener::exitClass_constructor_declaration(
    SV3_1aParser::Class_constructor_declarationContext *ctx) {
  if (ctx->ENDFUNCTION())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDFUNCTION(),
               VObjectType::slEndfunction);
  addVObject(ctx, VObjectType::slClass_constructor_declaration);
}

void SV3_1aTreeShapeListener::exitFunction_body_declaration(
    SV3_1aParser::Function_body_declarationContext *ctx) {
  if (ctx->ENDFUNCTION())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDFUNCTION(),
               VObjectType::slEndfunction);
  addVObject(ctx, VObjectType::slFunction_body_declaration);
}

void SV3_1aTreeShapeListener::exitTask_body_declaration(
    SV3_1aParser::Task_body_declarationContext *ctx) {
  if (ctx->ENDTASK())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDTASK(),
               VObjectType::slEndtask);
  addVObject(ctx, VObjectType::slTask_body_declaration);
}

void SV3_1aTreeShapeListener::exitJump_statement(
    SV3_1aParser::Jump_statementContext *ctx) {
  if (ctx->BREAK()) {
    addVObject((antlr4::ParserRuleContext *)ctx->BREAK(),
               VObjectType::slBreakStmt);
  } else if (ctx->CONTINUE()) {
    addVObject((antlr4::ParserRuleContext *)ctx->CONTINUE(),
               VObjectType::slContinueStmt);
  } else if (ctx->RETURN()) {
    addVObject((antlr4::ParserRuleContext *)ctx->RETURN(),
               VObjectType::slReturnStmt);
  }
  addVObject(ctx, VObjectType::slJump_statement);
}

void SV3_1aTreeShapeListener::exitClass_declaration(
    SV3_1aParser::Class_declarationContext *ctx) {
  if (ctx->VIRTUAL())
    addVObject((antlr4::ParserRuleContext *)ctx->VIRTUAL(),
               VObjectType::slVirtual);
  if (ctx->IMPLEMENTS())
    addVObject((antlr4::ParserRuleContext *)ctx->IMPLEMENTS(),
               VObjectType::slImplements);
  if (ctx->EXTENDS())
    addVObject((antlr4::ParserRuleContext *)ctx->EXTENDS(),
               VObjectType::slExtends);
  if (ctx->ENDCLASS())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDCLASS(),
               VObjectType::slEndclass);
  addVObject(ctx, VObjectType::slClass_declaration);
}

void SV3_1aTreeShapeListener::exitInterface_class_declaration(
    SV3_1aParser::Interface_class_declarationContext *ctx) {
  if (ctx->EXTENDS())
    addVObject((antlr4::ParserRuleContext *)ctx->EXTENDS(),
               VObjectType::slExtends);
  if (ctx->ENDCLASS())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDCLASS(),
               VObjectType::slEndclass);
  addVObject(ctx, VObjectType::slInterface_class_declaration);
}

void SV3_1aTreeShapeListener::exitChecker_declaration(
    SV3_1aParser::Checker_declarationContext *ctx) {
  if (ctx->ENDCHECKER())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDCHECKER(),
               VObjectType::slEndchecker);
  addVObject(ctx, VObjectType::slChecker_declaration);
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
  if (type == IncludeFileInfo::PUSH) {
    // Push
    IncludeFileInfo info(startLine,
                         m_pf->getSymbolTable()->registerSymbol(file),
                         lineCol.first, IncludeFileInfo::PUSH);
    m_includeFileInfo.push(info);
  } else if (type == IncludeFileInfo::POP) {
    // Pop
    if (m_includeFileInfo.size()) m_includeFileInfo.pop();
    if (m_includeFileInfo.size()) {
      m_includeFileInfo.top().m_sectionFile =
          m_pf->getSymbolTable()->registerSymbol(file);
      m_includeFileInfo.top().m_originalLine = lineCol.first /*+ m_lineOffset*/;
      m_includeFileInfo.top().m_sectionStartLine = startLine;
      m_includeFileInfo.top().m_type = IncludeFileInfo::POP;
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
  if (ctx->EXTERN() == nullptr)
    if (ctx->ENDINTERFACE())
      addVObject((antlr4::ParserRuleContext *)ctx->ENDINTERFACE(),
                 VObjectType::slEndinterface);
  addVObject(ctx, VObjectType::slInterface_declaration);
  m_nestedElements.pop();
}

void SV3_1aTreeShapeListener::exitProperty_expr(
    SV3_1aParser::Property_exprContext *ctx) {
  if (ctx->CASE()) {
    addVObject((antlr4::ParserRuleContext *)ctx->CASE(), VObjectType::slCase);
  }
  if (ctx->ENDCASE()) {
    addVObject((antlr4::ParserRuleContext *)ctx->ENDCASE(),
               VObjectType::slEndcase);
  } else if (ctx->OR()) {
    addVObject((antlr4::ParserRuleContext *)ctx->OR(), VObjectType::slOR);
  } else if (ctx->AND()) {
    addVObject((antlr4::ParserRuleContext *)ctx->AND(), VObjectType::slAND);
  } else if (ctx->IF()) {
    addVObject((antlr4::ParserRuleContext *)ctx->IF(), VObjectType::slIF);
  } else if (ctx->STRONG()) {
    addVObject((antlr4::ParserRuleContext *)ctx->STRONG(),
               VObjectType::slSTRONG);
  } else if (ctx->WEAK()) {
    addVObject((antlr4::ParserRuleContext *)ctx->WEAK(), VObjectType::slWEAK);
  } else if (ctx->NOT()) {
    addVObject((antlr4::ParserRuleContext *)ctx->NOT(), VObjectType::slNOT);
  } else if (ctx->OVERLAP_IMPLY()) {
    addVObject((antlr4::ParserRuleContext *)ctx->OVERLAP_IMPLY(),
               VObjectType::slOVERLAP_IMPLY);
  } else if (ctx->NON_OVERLAP_IMPLY()) {
    addVObject((antlr4::ParserRuleContext *)ctx->NON_OVERLAP_IMPLY(),
               VObjectType::slNON_OVERLAP_IMPLY);
  } else if (ctx->OVERLAPPED()) {
    addVObject((antlr4::ParserRuleContext *)ctx->OVERLAPPED(),
               VObjectType::slOVERLAPPED);
  } else if (ctx->NONOVERLAPPED()) {
    addVObject((antlr4::ParserRuleContext *)ctx->NONOVERLAPPED(),
               VObjectType::slNONOVERLAPPED);
  } else if (ctx->S_NEXTTIME()) {
    addVObject((antlr4::ParserRuleContext *)ctx->S_NEXTTIME(),
               VObjectType::slS_NEXTTIME);
  } else if (ctx->ALWAYS()) {
    addVObject((antlr4::ParserRuleContext *)ctx->ALWAYS(),
               VObjectType::slALWAYS);
  } else if (ctx->S_ALWAYS()) {
    addVObject((antlr4::ParserRuleContext *)ctx->S_ALWAYS(),
               VObjectType::slS_ALWAYS);
  } else if (ctx->S_EVENTUALLY()) {
    addVObject((antlr4::ParserRuleContext *)ctx->S_EVENTUALLY(),
               VObjectType::slS_EVENTUALLY);
  } else if (ctx->EVENTUALLY()) {
    addVObject((antlr4::ParserRuleContext *)ctx->EVENTUALLY(),
               VObjectType::slEVENTUALLY);
  } else if (ctx->UNTIL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->UNTIL(), VObjectType::slUNTIL);
  } else if (ctx->S_UNTIL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->S_UNTIL(),
               VObjectType::slS_UNTIL);
  } else if (ctx->IMPLIES()) {
    addVObject((antlr4::ParserRuleContext *)ctx->IMPLIES(),
               VObjectType::slIMPLIES);
  } else if (ctx->IFF()) {
    addVObject((antlr4::ParserRuleContext *)ctx->IFF(), VObjectType::slIFF);
  } else if (ctx->ACCEPT_ON()) {
    addVObject((antlr4::ParserRuleContext *)ctx->ACCEPT_ON(),
               VObjectType::slACCEPT_ON);
  } else if (ctx->REJECT_ON()) {
    addVObject((antlr4::ParserRuleContext *)ctx->REJECT_ON(),
               VObjectType::slREJECT_ON);
  } else if (ctx->SYNC_ACCEPT_ON()) {
    addVObject((antlr4::ParserRuleContext *)ctx->SYNC_ACCEPT_ON(),
               VObjectType::slSYNC_ACCEPT_ON);
  } else if (ctx->SYNC_REJECT_ON()) {
    addVObject((antlr4::ParserRuleContext *)ctx->SYNC_REJECT_ON(),
               VObjectType::slSYNC_REJECT_ON);
  }
  addVObject(ctx, VObjectType::slProperty_expr);
}

void SV3_1aTreeShapeListener::exitGenerate_module_case_statement(
    SV3_1aParser::Generate_module_case_statementContext *ctx) {
  if (ctx->ENDCASE())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDCASE(),
               VObjectType::slEndcase);
  addVObject(ctx, VObjectType::slGenerate_module_case_statement);
}

void SV3_1aTreeShapeListener::exitGenerate_interface_case_statement(
    SV3_1aParser::Generate_interface_case_statementContext *ctx) {
  if (ctx->ENDCASE())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDCASE(),
               VObjectType::slEndcase);
  addVObject(ctx, VObjectType::slGenerate_interface_case_statement);
}

void SV3_1aTreeShapeListener::exitCase_generate_construct(
    SV3_1aParser::Case_generate_constructContext *ctx) {
  if (ctx->ENDCASE())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDCASE(),
               VObjectType::slEndcase);
  addVObject(ctx, VObjectType::slCase_generate_construct);
}

void SV3_1aTreeShapeListener::exitCase_statement(
    SV3_1aParser::Case_statementContext *ctx) {
  if (ctx->ENDCASE())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDCASE(),
               VObjectType::slEndcase);
  addVObject(ctx, VObjectType::slCase_statement);
}

void SV3_1aTreeShapeListener::exitRandcase_statement(
    SV3_1aParser::Randcase_statementContext *ctx) {
  if (ctx->ENDCASE())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDCASE(),
               VObjectType::slEndcase);
  addVObject(ctx, VObjectType::slRandcase_statement);
}

void SV3_1aTreeShapeListener::exitRs_case(SV3_1aParser::Rs_caseContext *ctx) {
  if (ctx->ENDCASE())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDCASE(),
               VObjectType::slEndcase);
  addVObject(ctx, VObjectType::slRs_case);
}

void SV3_1aTreeShapeListener::exitSequence_declaration(
    SV3_1aParser::Sequence_declarationContext *ctx) {
  if (ctx->ENDSEQUENCE())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDSEQUENCE(),
               VObjectType::slEndsequence);
  addVObject(ctx, VObjectType::slSequence_declaration);
}

void SV3_1aTreeShapeListener::exitRandsequence_statement(
    SV3_1aParser::Randsequence_statementContext *ctx) {
  if (ctx->ENDSEQUENCE())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDSEQUENCE(),
               VObjectType::slEndsequence);
  addVObject(ctx, VObjectType::slRandsequence_statement);
}

void SV3_1aTreeShapeListener::exitSeq_block(
    SV3_1aParser::Seq_blockContext *ctx) {
  if (ctx->END())
    addVObject((antlr4::ParserRuleContext *)ctx->END(), VObjectType::slEnd);
  addVObject(ctx, VObjectType::slSeq_block);
}

void SV3_1aTreeShapeListener::exitGenerate_module_named_block(
    SV3_1aParser::Generate_module_named_blockContext *ctx) {
  if (ctx->END())
    addVObject((antlr4::ParserRuleContext *)ctx->END(), VObjectType::slEnd);
  addVObject(ctx, VObjectType::slGenerate_module_named_block);
}

void SV3_1aTreeShapeListener::exitGenerate_module_block(
    SV3_1aParser::Generate_module_blockContext *ctx) {
  if (ctx->END())
    addVObject((antlr4::ParserRuleContext *)ctx->END(), VObjectType::slEnd);
  addVObject(ctx, VObjectType::slGenerate_module_block);
}

void SV3_1aTreeShapeListener::exitGenerate_interface_named_block(
    SV3_1aParser::Generate_interface_named_blockContext *ctx) {
  if (ctx->END())
    addVObject((antlr4::ParserRuleContext *)ctx->END(), VObjectType::slEnd);
  addVObject(ctx, VObjectType::slGenerate_interface_named_block);
}

void SV3_1aTreeShapeListener::exitGenerate_interface_block(
    SV3_1aParser::Generate_interface_blockContext *ctx) {
  if (ctx->END())
    addVObject((antlr4::ParserRuleContext *)ctx->END(), VObjectType::slEnd);
  addVObject(ctx, VObjectType::slGenerate_interface_block);
}

void SV3_1aTreeShapeListener::exitGenerate_block(
    SV3_1aParser::Generate_blockContext *ctx) {
  if (ctx->END())
    addVObject((antlr4::ParserRuleContext *)ctx->END(), VObjectType::slEnd);
  addVObject(ctx, VObjectType::slGenerate_block);
}

void SV3_1aTreeShapeListener::exitNamed_port_connection(
    SV3_1aParser::Named_port_connectionContext *ctx) {
  if (ctx->DOTSTAR())
    addVObject((antlr4::ParserRuleContext *)ctx->DOTSTAR(),
               VObjectType::slDotStar);
  if (ctx->OPEN_PARENS())
    addVObject((antlr4::ParserRuleContext *)ctx->OPEN_PARENS(),
               VObjectType::slOpenParens);
  if (ctx->CLOSE_PARENS())
    addVObject((antlr4::ParserRuleContext *)ctx->CLOSE_PARENS(),
               VObjectType::slCloseParens);
  addVObject(ctx, VObjectType::slNamed_port_connection);
}

void SV3_1aTreeShapeListener::exitPattern(SV3_1aParser::PatternContext *ctx) {
  if (ctx->DOT())
    addVObject((antlr4::ParserRuleContext *)ctx->DOT(), VObjectType::slDot);
  else if (ctx->DOTSTAR())
    addVObject((antlr4::ParserRuleContext *)ctx->DOTSTAR(),
               VObjectType::slDotStar);
  else if (ctx->TAGGED())
    addVObject((antlr4::ParserRuleContext *)ctx->TAGGED(),
               VObjectType::slTagged);

  addVObject(ctx, VObjectType::slPattern);
}

void SV3_1aTreeShapeListener::exitSpecify_block(
    SV3_1aParser::Specify_blockContext *ctx) {
  if (ctx->ENDSPECIFY())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDSPECIFY(),
               VObjectType::slEndspecify);
  addVObject(ctx, VObjectType::slSpecify_block);
}

void SV3_1aTreeShapeListener::exitConfig_declaration(
    SV3_1aParser::Config_declarationContext *ctx) {
  if (ctx->ENDCONFIG())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDCONFIG(),
               VObjectType::slEndconfig);
  addVObject(ctx, VObjectType::slConfig_declaration);
}

void SV3_1aTreeShapeListener::exitDpi_import_export(
    SV3_1aParser::Dpi_import_exportContext *ctx) {
  if (ctx->IMPORT())
    addVObject((antlr4::ParserRuleContext *)ctx->IMPORT(),
               VObjectType::slImport);
  if (ctx->EXPORT())
    addVObject((antlr4::ParserRuleContext *)ctx->EXPORT(),
               VObjectType::slExport);
  addVObject(ctx, VObjectType::slDpi_import_export);
}

void SV3_1aTreeShapeListener::exitProperty_declaration(
    SV3_1aParser::Property_declarationContext *ctx) {
  if (ctx->ENDPROPERTY())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDPROPERTY(),
               VObjectType::slEndproperty);
  addVObject(ctx, VObjectType::slProperty_declaration);
}

void SV3_1aTreeShapeListener::exitCovergroup_declaration(
    SV3_1aParser::Covergroup_declarationContext *ctx) {
  if (ctx->ENDGROUP())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDGROUP(),
               VObjectType::slEndgroup);
  addVObject(ctx, VObjectType::slCovergroup_declaration);
}

void SV3_1aTreeShapeListener::exitGenerated_module_instantiation(
    SV3_1aParser::Generated_module_instantiationContext *ctx) {
  if (ctx->ENDGENERATE())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDGENERATE(),
               VObjectType::slEndgenerate);
  addVObject(ctx, VObjectType::slGenerated_module_instantiation);
}

void SV3_1aTreeShapeListener::exitGenerated_interface_instantiation(
    SV3_1aParser::Generated_interface_instantiationContext *ctx) {
  if (ctx->ENDGENERATE())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDGENERATE(),
               VObjectType::slEndgenerate);
  addVObject(ctx, VObjectType::slGenerated_interface_instantiation);
}

void SV3_1aTreeShapeListener::exitGenerate_region(
    SV3_1aParser::Generate_regionContext *ctx) {
  if (ctx->ENDGENERATE())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDGENERATE(),
               VObjectType::slEndgenerate);
  addVObject(ctx, VObjectType::slGenerate_region);
}

void SV3_1aTreeShapeListener::exitUdp_declaration(
    SV3_1aParser::Udp_declarationContext *ctx) {
  if (ctx->ENDPRIMITIVE())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDPRIMITIVE(),
               VObjectType::slEndprimitive);
  addVObject(ctx, VObjectType::slUdp_declaration);
}

void SV3_1aTreeShapeListener::exitCombinational_body(
    SV3_1aParser::Combinational_bodyContext *ctx) {
  if (ctx->ENDTABLE())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDTABLE(),
               VObjectType::slEndtable);
  addVObject(ctx, VObjectType::slCombinational_body);
}

void SV3_1aTreeShapeListener::exitSequential_body(
    SV3_1aParser::Sequential_bodyContext *ctx) {
  if (ctx->ENDTABLE())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDTABLE(),
               VObjectType::slEndtable);
  addVObject(ctx, VObjectType::slSequential_body);
}

void SV3_1aTreeShapeListener::exitClocking_declaration(
    SV3_1aParser::Clocking_declarationContext *ctx) {
  if (ctx->DEFAULT())
    addVObject((antlr4::ParserRuleContext *)ctx->DEFAULT(),
               VObjectType::slDefault);
  if (ctx->GLOBAL())
    addVObject((antlr4::ParserRuleContext *)ctx->GLOBAL(),
               VObjectType::slGlobal);
  if (ctx->ENDCLOCKING())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDCLOCKING(),
               VObjectType::slEndclocking);
  addVObject(ctx, VObjectType::slClocking_declaration);
}

void SV3_1aTreeShapeListener::exitPackage_declaration(
    SV3_1aParser::Package_declarationContext *ctx) {
  if (ctx->ENDPACKAGE())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDPACKAGE(),
               VObjectType::slEndpackage);
  addVObject(ctx, VObjectType::slPackage_declaration);
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

void SV3_1aTreeShapeListener::enterTimescale_directive(
    SV3_1aParser::Timescale_directiveContext *ctx) {
  TimeInfo compUnitTimeInfo;
  compUnitTimeInfo.m_type = TimeInfo::Type::Timescale;
  compUnitTimeInfo.m_fileId = m_pf->getFileId(0);
  std::pair<int, int> lineCol =
      ParseUtils::getLineColumn(ctx->TICK_TIMESCALE());
  compUnitTimeInfo.m_line = lineCol.first;
  std::regex base_regex("`timescale([0-9]+)([mnsupf]+)/([0-9]+)([mnsupf]+)");
  std::smatch base_match;
  const std::string value = ctx->getText();
  if (std::regex_match(value, base_match, base_regex)) {
    std::ssub_match base1_sub_match = base_match[1];
    std::string base1 = base1_sub_match.str();
    compUnitTimeInfo.m_timeUnitValue = atoi(base1.c_str());
    if ((compUnitTimeInfo.m_timeUnitValue != 1) &&
        (compUnitTimeInfo.m_timeUnitValue != 10) &&
        (compUnitTimeInfo.m_timeUnitValue != 100)) {
      logError(ErrorDefinition::PA_TIMESCALE_INVALID_VALUE, ctx, base1);
    }
    compUnitTimeInfo.m_timeUnit = TimeInfo::unitFromString(base_match[2].str());
    std::ssub_match base2_sub_match = base_match[3];
    std::string base2 = base2_sub_match.str();
    compUnitTimeInfo.m_timePrecisionValue = atoi(base2.c_str());
    if ((compUnitTimeInfo.m_timePrecisionValue != 1) &&
        (compUnitTimeInfo.m_timePrecisionValue != 10) &&
        (compUnitTimeInfo.m_timePrecisionValue != 100)) {
      logError(ErrorDefinition::PA_TIMESCALE_INVALID_VALUE, ctx, base2);
    }
    uint64_t unitInFs = TimeInfo::femtoSeconds(
        compUnitTimeInfo.m_timeUnit, compUnitTimeInfo.m_timeUnitValue);
    compUnitTimeInfo.m_timePrecision =
        TimeInfo::unitFromString(base_match[4].str());
    uint64_t precisionInFs =
        TimeInfo::femtoSeconds(compUnitTimeInfo.m_timePrecision,
                               compUnitTimeInfo.m_timePrecisionValue);
    if (unitInFs < precisionInFs) {
      logError(ErrorDefinition::PA_TIMESCALE_INVALID_SCALE, ctx, "");
    }
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

void SV3_1aTreeShapeListener::exitTime_literal(
    SV3_1aParser::Time_literalContext *ctx) {
  auto pair = getTimeValue(ctx);
  uint64_t value = pair.first;
  if (ctx->Integral_number())
    addVObject((antlr4::ParserRuleContext *)ctx->Integral_number(),
               std::to_string(value), VObjectType::slIntConst);
  else if (ctx->Real_number())
    addVObject((antlr4::ParserRuleContext *)ctx->Real_number(),
               std::to_string(value), VObjectType::slIntConst);
  const std::string &s = ctx->time_unit()->getText();
  if ((s == "s") || (s == "ms") || (s == "us") || (s == "ns") || (s == "ps") ||
      (s == "fs")) {
  } else {
    logError(ErrorDefinition::COMP_ILLEGAL_TIMESCALE, ctx, s);
  }
  addVObject(ctx->time_unit(), s, VObjectType::slTime_unit);
  addVObject(ctx, VObjectType::slTime_literal);
}

void SV3_1aTreeShapeListener::exitTime_unit(
    SV3_1aParser::Time_unitContext *ctx) {
  addVObject(ctx, ctx->getText(), VObjectType::slTime_unit);
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

void SV3_1aTreeShapeListener::exitUnbased_unsized_literal(
    SV3_1aParser::Unbased_unsized_literalContext *ctx) {
  std::string s = ctx->Simple_identifier()->getText();
  VObjectType type = VObjectType::slZ;
  if (s == "z" || s == "Z") {
    type = VObjectType::slZ;
  } else if (s == "x" || s == "X") {
    type = VObjectType::slX;
  }
  addVObject(ctx, s, type);
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
    addVObject(ctx, ctx->Pound_delay()->getText(), VObjectType::slIntConst);
  } else if (ctx->Pound_Pound_delay()) {
    addVObject(ctx, ctx->Pound_Pound_delay()->getText(),
               VObjectType::slPound_Pound_delay);
  } else if (ctx->delay_value()) {
    addVObject(ctx, ctx->delay_value()->getText(), VObjectType::slIntConst);
  }
}

void SV3_1aTreeShapeListener::exitString_value(
    SV3_1aParser::String_valueContext *ctx) {
  std::string ident;

  ident = ctx->String()->getText();

  std::regex escaped(std::string(EscapeSequence) + std::string("(.*?)") +
                     EscapeSequence);
  std::smatch match;
  while (std::regex_search(ident, match, escaped)) {
    std::string var = "\\" + match[1].str() + " ";
    ident = ident.replace(match.position(0), match.length(0), var);
  }

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

void SV3_1aTreeShapeListener::exitUnique_priority(
    SV3_1aParser::Unique_priorityContext *ctx) {
  if (ctx->PRIORITY()) {
    addVObject((antlr4::ParserRuleContext *)ctx->PRIORITY(),
               VObjectType::slPriority);
  } else if (ctx->UNIQUE()) {
    addVObject((antlr4::ParserRuleContext *)ctx->UNIQUE(),
               VObjectType::slUnique);
  } else if (ctx->UNIQUE0()) {
    addVObject((antlr4::ParserRuleContext *)ctx->UNIQUE0(),
               VObjectType::slUnique0);
  }
  addVObject(ctx, VObjectType::slUnique_priority);
}

void SV3_1aTreeShapeListener::exitCase_keyword(
    SV3_1aParser::Case_keywordContext *ctx) {
  if (ctx->CASE()) {
    addVObject((antlr4::ParserRuleContext *)ctx->CASE(), VObjectType::slCase);
  } else if (ctx->CASEX()) {
    addVObject((antlr4::ParserRuleContext *)ctx->CASEX(), VObjectType::slCaseX);
  } else if (ctx->CASEZ()) {
    addVObject((antlr4::ParserRuleContext *)ctx->CASEZ(), VObjectType::slCaseZ);
  }
  addVObject(ctx, VObjectType::slCase_keyword);
}

void SV3_1aTreeShapeListener::exitPart_select_op_column(
    SV3_1aParser::Part_select_op_columnContext *ctx) {
  if (ctx->INC_PART_SELECT_OP()) {
    addVObject(ctx, VObjectType::slIncPartSelectOp);
  } else if (ctx->DEC_PART_SELECT_OP()) {
    addVObject(ctx, VObjectType::slDecPartSelectOp);
  } else if (ctx->COLUMN()) {
    addVObject(ctx, VObjectType::slColumnPartSelectOp);
  }
}

void SV3_1aTreeShapeListener::exitPart_select_op(
    SV3_1aParser::Part_select_opContext *ctx) {
  if (ctx->INC_PART_SELECT_OP()) {
    addVObject(ctx, VObjectType::slIncPartSelectOp);
  } else if (ctx->DEC_PART_SELECT_OP()) {
    addVObject(ctx, VObjectType::slDecPartSelectOp);
  }
}

void SV3_1aTreeShapeListener::exitSystem_task_names(
    SV3_1aParser::System_task_namesContext *ctx) {
  std::string ident = ctx->getText();
  if (ctx->TIME())
    addVObject((antlr4::ParserRuleContext *)ctx->TIME(), ident,
               VObjectType::slStringConst);
  else if (ctx->REALTIME())
    addVObject((antlr4::ParserRuleContext *)ctx->REALTIME(), ident,
               VObjectType::slStringConst);
  else if (ctx->ASSERT())
    addVObject((antlr4::ParserRuleContext *)ctx->ASSERT(), ident,
               VObjectType::slStringConst);
  else if (ctx->Simple_identifier().size())
    addVObject((antlr4::ParserRuleContext *)ctx->Simple_identifier()[0], ident,
               VObjectType::slStringConst);
  else if (ctx->SIGNED())
    addVObject((antlr4::ParserRuleContext *)ctx->SIGNED(), ident,
               VObjectType::slStringConst);
  else if (ctx->UNSIGNED())
    addVObject((antlr4::ParserRuleContext *)ctx->UNSIGNED(), ident,
               VObjectType::slStringConst);
  addVObject(ctx, VObjectType::slSystem_task_names);
}

void SV3_1aTreeShapeListener::exitClass_type(
    SV3_1aParser::Class_typeContext *ctx) {
  std::string ident;
  antlr4::ParserRuleContext *childCtx = nullptr;
  if (ctx->Simple_identifier()) {
    childCtx = (antlr4::ParserRuleContext *)ctx->Simple_identifier();
    ident = ctx->Simple_identifier()->getText();
  } else if (ctx->Escaped_identifier()) {
    childCtx = (antlr4::ParserRuleContext *)ctx->Escaped_identifier();
    ident = ctx->Escaped_identifier()->getText();
    ident.erase(0, 3);
    ident.erase(ident.size() - 3, 3);
  } else if (ctx->THIS()) {
    childCtx = (antlr4::ParserRuleContext *)ctx->THIS();
    ident = ctx->THIS()->getText();
  } else if (ctx->RANDOMIZE()) {
    childCtx = (antlr4::ParserRuleContext *)ctx->RANDOMIZE();
    ident = ctx->RANDOMIZE()->getText();
  } else if (ctx->SAMPLE()) {
    childCtx = (antlr4::ParserRuleContext *)ctx->SAMPLE();
    ident = ctx->SAMPLE()->getText();
  } else if (ctx->DOLLAR_UNIT()) {
    childCtx = (antlr4::ParserRuleContext *)ctx->DOLLAR_UNIT();
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

  for (auto &o : ctx->children) {
    antlr4::tree::TerminalNode *tnode =
        dynamic_cast<antlr4::tree::TerminalNode *>(o);
    if (tnode != nullptr) {
      antlr4::Token *symbol = tnode->getSymbol();
      if (symbol->getType() == SV3_1aParser::Simple_identifier ||
          symbol->getType() == SV3_1aParser::Escaped_identifier) {
        ident = tnode->getText();
        ident = std::regex_replace(ident, std::regex(EscapeSequence), "");
        addVObject((antlr4::ParserRuleContext *)tnode, ident,
                   VObjectType::slStringConst);
      } else if (symbol->getType() == SV3_1aParser::THIS ||
                 symbol->getType() == SV3_1aParser::RANDOMIZE ||
                 symbol->getType() == SV3_1aParser::SAMPLE) {
        ident = tnode->getText();
        addVObject((antlr4::ParserRuleContext *)tnode, ident,
                   VObjectType::slStringConst);
      }
    }
  }

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

void SV3_1aTreeShapeListener::exitAnonymous_program(
    SV3_1aParser::Anonymous_programContext *ctx) {
  if (ctx->ENDPROGRAM())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDPROGRAM(),
               VObjectType::slEndprogram);
  addVObject(ctx, VObjectType::slAnonymous_program);
}

void SV3_1aTreeShapeListener::exitProgram_declaration(
    SV3_1aParser::Program_declarationContext *ctx) {
  if (ctx->ENDPROGRAM())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDPROGRAM(),
               VObjectType::slEndprogram);
  addVObject(ctx, VObjectType::slProgram_declaration);
}

void SV3_1aTreeShapeListener::exitProcedural_continuous_assignment(
    SV3_1aParser::Procedural_continuous_assignmentContext *ctx) {
  if (ctx->ASSIGN()) {
    addVObject((antlr4::ParserRuleContext *)ctx->ASSIGN(),
               VObjectType::slAssign);
  } else if (ctx->DEASSIGN()) {
    addVObject((antlr4::ParserRuleContext *)ctx->DEASSIGN(),
               VObjectType::slDeassign);
  } else if (ctx->FORCE()) {
    addVObject((antlr4::ParserRuleContext *)ctx->FORCE(), VObjectType::slForce);
  } else if (ctx->RELEASE()) {
    addVObject((antlr4::ParserRuleContext *)ctx->RELEASE(),
               VObjectType::slRelease);
  }
  addVObject(ctx, VObjectType::slProcedural_continuous_assignment);
}

void SV3_1aTreeShapeListener::exitDrive_strength(
    SV3_1aParser::Drive_strengthContext *ctx) {
  if (ctx->SUPPLY0()) {
    addVObject((antlr4::ParserRuleContext *)ctx->SUPPLY0(),
               VObjectType::slSupply0);
  } else if (ctx->STRONG0()) {
    addVObject((antlr4::ParserRuleContext *)ctx->STRONG0(),
               VObjectType::slStrong0);
  } else if (ctx->PULL0()) {
    addVObject((antlr4::ParserRuleContext *)ctx->PULL0(), VObjectType::slPull0);
  } else if (ctx->WEAK0()) {
    addVObject((antlr4::ParserRuleContext *)ctx->WEAK0(), VObjectType::slWeak0);
  }
  if (ctx->SUPPLY1()) {
    addVObject((antlr4::ParserRuleContext *)ctx->SUPPLY1(),
               VObjectType::slSupply1);
  } else if (ctx->STRONG1()) {
    addVObject((antlr4::ParserRuleContext *)ctx->STRONG1(),
               VObjectType::slStrong1);
  } else if (ctx->PULL1()) {
    addVObject((antlr4::ParserRuleContext *)ctx->PULL1(), VObjectType::slPull1);
  } else if (ctx->WEAK1()) {
    addVObject((antlr4::ParserRuleContext *)ctx->WEAK1(), VObjectType::slWeak1);
  }

  if (ctx->HIGHZ0()) {
    addVObject((antlr4::ParserRuleContext *)ctx->HIGHZ0(),
               VObjectType::slHighZ0);
  } else if (ctx->HIGHZ1()) {
    addVObject((antlr4::ParserRuleContext *)ctx->HIGHZ1(),
               VObjectType::slHighZ1);
  }
  addVObject(ctx, VObjectType::slDrive_strength);
}

void SV3_1aTreeShapeListener::exitStrength0(
    SV3_1aParser::Strength0Context *ctx) {
  if (ctx->SUPPLY0()) {
    addVObject((antlr4::ParserRuleContext *)ctx->SUPPLY0(),
               VObjectType::slSupply0);
  } else if (ctx->STRONG0()) {
    addVObject((antlr4::ParserRuleContext *)ctx->STRONG0(),
               VObjectType::slStrong0);
  } else if (ctx->PULL0()) {
    addVObject((antlr4::ParserRuleContext *)ctx->PULL0(), VObjectType::slPull0);
  } else if (ctx->WEAK0()) {
    addVObject((antlr4::ParserRuleContext *)ctx->WEAK0(), VObjectType::slWeak0);
  }
  addVObject(ctx, VObjectType::slStrength0);
}

void SV3_1aTreeShapeListener::exitAction_block(
    SV3_1aParser::Action_blockContext *ctx) {
  if (ctx->ELSE()) {
    addVObject((antlr4::ParserRuleContext *)ctx->ELSE(), VObjectType::slElse);
  }
  addVObject(ctx, VObjectType::slAction_block);
}

void SV3_1aTreeShapeListener::exitEvent_trigger(
    SV3_1aParser::Event_triggerContext *ctx) {
  if (ctx->IMPLY())
    addVObject((antlr4::ParserRuleContext *)ctx->IMPLY(),
               VObjectType::slBinOp_Imply);
  if (ctx->NON_BLOCKING_TRIGGER_EVENT_OP())
    addVObject(
        (antlr4::ParserRuleContext *)ctx->NON_BLOCKING_TRIGGER_EVENT_OP(),
        VObjectType::slNonBlockingTriggerEvent);
  addVObject(ctx, VObjectType::slEvent_trigger);
}

void SV3_1aTreeShapeListener::exitStrength1(
    SV3_1aParser::Strength1Context *ctx) {
  if (ctx->SUPPLY1()) {
    addVObject((antlr4::ParserRuleContext *)ctx->SUPPLY1(),
               VObjectType::slSupply1);
  } else if (ctx->STRONG1()) {
    addVObject((antlr4::ParserRuleContext *)ctx->STRONG1(),
               VObjectType::slStrong1);
  } else if (ctx->PULL1()) {
    addVObject((antlr4::ParserRuleContext *)ctx->PULL1(), VObjectType::slPull1);
  } else if (ctx->WEAK1()) {
    addVObject((antlr4::ParserRuleContext *)ctx->WEAK1(), VObjectType::slWeak1);
  }
  addVObject(ctx, VObjectType::slStrength1);
}

void SV3_1aTreeShapeListener::exitCharge_strength(
    SV3_1aParser::Charge_strengthContext *ctx) {
  if (ctx->SMALL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->SMALL(), VObjectType::slSmall);
  } else if (ctx->MEDIUM()) {
    addVObject((antlr4::ParserRuleContext *)ctx->MEDIUM(),
               VObjectType::slMedium);
  } else if (ctx->LARGE()) {
    addVObject((antlr4::ParserRuleContext *)ctx->LARGE(), VObjectType::slLarge);
  }
  addVObject(ctx, VObjectType::slCharge_strength);
}

void SV3_1aTreeShapeListener::exitStream_operator(
    SV3_1aParser::Stream_operatorContext *ctx) {
  if (ctx->SHIFT_RIGHT()) {
    addVObject((antlr4::ParserRuleContext *)ctx->SHIFT_RIGHT(),
               VObjectType::slBinOp_ShiftRight);
  } else if (ctx->SHIFT_LEFT()) {
    addVObject((antlr4::ParserRuleContext *)ctx->SHIFT_LEFT(),
               VObjectType::slBinOp_ShiftLeft);
  }
  addVObject(ctx, VObjectType::slStream_operator);
}

void SV3_1aTreeShapeListener::exitLoop_statement(
    SV3_1aParser::Loop_statementContext *ctx) {
  if (ctx->DO()) {
    addVObject((antlr4::ParserRuleContext *)ctx->DO(), VObjectType::slDo);
  } else if (ctx->FOREVER()) {
    addVObject((antlr4::ParserRuleContext *)ctx->FOREVER(),
               VObjectType::slForever);
  } else if (ctx->REPEAT()) {
    addVObject((antlr4::ParserRuleContext *)ctx->REPEAT(),
               VObjectType::slRepeat);
  } else if (ctx->WHILE()) {
    addVObject((antlr4::ParserRuleContext *)ctx->WHILE(), VObjectType::slWhile);
  } else if (ctx->FOR()) {
    addVObject((antlr4::ParserRuleContext *)ctx->FOR(), VObjectType::slFor);
  } else if (ctx->FOREACH()) {
    addVObject((antlr4::ParserRuleContext *)ctx->FOREACH(),
               VObjectType::slForeach);
  }
  addVObject(ctx, VObjectType::slLoop_statement);
}

void SV3_1aTreeShapeListener::exitPackage_scope(
    SV3_1aParser::Package_scopeContext *ctx) {
  std::string ident;
  antlr4::ParserRuleContext *childCtx = nullptr;
  if (ctx->Simple_identifier()) {
    childCtx = (antlr4::ParserRuleContext *)ctx->Simple_identifier();
    ident = ctx->Simple_identifier()->getText();
  } else if (ctx->Escaped_identifier()) {
    childCtx = (antlr4::ParserRuleContext *)ctx->Escaped_identifier();
    ident = ctx->Escaped_identifier()->getText();
    std::regex escaped(std::string(EscapeSequence) + std::string("(.*?)") +
                       EscapeSequence);
    std::smatch match;
    while (std::regex_search(ident, match, escaped)) {
      std::string var = match[1].str();
      ident = ident.replace(match.position(0), match.length(0), var);
    }
  } else if (ctx->THIS()) {
    childCtx = (antlr4::ParserRuleContext *)ctx->THIS();
    ident = ctx->THIS()->getText();
  } else if (ctx->RANDOMIZE()) {
    childCtx = (antlr4::ParserRuleContext *)ctx->RANDOMIZE();
    ident = ctx->RANDOMIZE()->getText();
  } else if (ctx->SAMPLE()) {
    childCtx = (antlr4::ParserRuleContext *)ctx->SAMPLE();
    ident = ctx->SAMPLE()->getText();
  } else if (ctx->DOLLAR_UNIT()) {
    childCtx = (antlr4::ParserRuleContext *)ctx->DOLLAR_UNIT();
    ident = ctx->DOLLAR_UNIT()->getText();
  }
  addVObject(childCtx, ident, VObjectType::slStringConst);
  addVObject(ctx, VObjectType::slPackage_scope);

  if (ident.size() > SV_MAX_IDENTIFIER_SIZE) {
    logError(ErrorDefinition::PA_MAX_LENGTH_IDENTIFIER, ctx, ident);
  }
}

void SV3_1aTreeShapeListener::exitPs_identifier(
    SV3_1aParser::Ps_identifierContext *ctx) {
  std::string ident;
  antlr4::ParserRuleContext *childCtx = nullptr;
  if (ctx->Simple_identifier().size()) {
    childCtx = (antlr4::ParserRuleContext *)ctx->Simple_identifier()[0];
    ident = ctx->Simple_identifier()[0]->getText();
    if (ctx->Simple_identifier().size() > 1) {
      ident += "::" + ctx->Simple_identifier()[1]->getText();
    }
  } else if (ctx->Escaped_identifier().size()) {
    childCtx = (antlr4::ParserRuleContext *)ctx->Escaped_identifier()[0];
    ident = ctx->Escaped_identifier()[0]->getText();
    std::regex escaped(std::string(EscapeSequence) + std::string("(.*?)") +
                       EscapeSequence);
    std::smatch match;
    while (std::regex_search(ident, match, escaped)) {
      std::string var = match[1].str();
      ident = ident.replace(match.position(0), match.length(0), var);
    }
  } else if (ctx->THIS().size()) {
    childCtx = (antlr4::ParserRuleContext *)ctx->THIS()[0];
    ident = ctx->THIS()[0]->getText();
  } else if (ctx->RANDOMIZE().size()) {
    childCtx = (antlr4::ParserRuleContext *)ctx->RANDOMIZE()[0];
    ident = ctx->RANDOMIZE()[0]->getText();
  } else if (ctx->SAMPLE().size()) {
    childCtx = (antlr4::ParserRuleContext *)ctx->SAMPLE()[0];
    ident = ctx->SAMPLE()[0]->getText();
  } else if (ctx->DOLLAR_UNIT()) {
    childCtx = (antlr4::ParserRuleContext *)ctx->DOLLAR_UNIT();
    ident = ctx->DOLLAR_UNIT()->getText();
  }
  addVObject(childCtx, ident, VObjectType::slStringConst);
  addVObject(ctx, VObjectType::slPs_identifier);

  if (ident.size() > SV_MAX_IDENTIFIER_SIZE) {
    logError(ErrorDefinition::PA_MAX_LENGTH_IDENTIFIER, ctx, ident);
  }
}

void SV3_1aTreeShapeListener::exitExpression(
    SV3_1aParser::ExpressionContext *ctx) {
  if (ctx->MATCHES()) {
    addVObject((antlr4::ParserRuleContext *)ctx->MATCHES(),
               VObjectType::slMatches);
  }
  if (ctx->PLUS()) {
    if (ctx->expression().size() == 1)
      addVObject((antlr4::ParserRuleContext *)ctx->PLUS(),
                 VObjectType::slUnary_Plus);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->PLUS(),
                 VObjectType::slBinOp_Plus);
  } else if (ctx->MINUS()) {
    if (ctx->expression().size() == 1)
      addVObject((antlr4::ParserRuleContext *)ctx->MINUS(),
                 VObjectType::slUnary_Minus);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->MINUS(),
                 VObjectType::slBinOp_Minus);
  } else if (ctx->BANG()) {
    addVObject((antlr4::ParserRuleContext *)ctx->BANG(),
               VObjectType::slUnary_Not);
  } else if (ctx->TILDA()) {
    addVObject((antlr4::ParserRuleContext *)ctx->TILDA(),
               VObjectType::slUnary_Tilda);
  } else if (ctx->BITW_AND()) {
    if (ctx->expression().size() == 1)
      addVObject((antlr4::ParserRuleContext *)ctx->BITW_AND(),
                 VObjectType::slUnary_BitwAnd);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->BITW_AND(),
                 VObjectType::slBinOp_BitwAnd);
  } else if (ctx->BITW_OR()) {
    if (ctx->expression().size() == 1)
      addVObject((antlr4::ParserRuleContext *)ctx->BITW_OR(),
                 VObjectType::slUnary_BitwOr);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->BITW_OR(),
                 VObjectType::slBinOp_BitwOr);
  } else if (ctx->BITW_XOR()) {
    if (ctx->expression().size() == 1)
      addVObject((antlr4::ParserRuleContext *)ctx->BITW_XOR(),
                 VObjectType::slUnary_BitwXor);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->BITW_XOR(),
                 VObjectType::slBinOp_BitwXor);
  } else if (ctx->REDUCTION_NAND()) {
    if (ctx->expression().size() == 1)
      addVObject((antlr4::ParserRuleContext *)ctx->REDUCTION_NAND(),
                 VObjectType::slUnary_ReductNand);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->REDUCTION_NAND(),
                 VObjectType::slBinOp_ReductNand);
  } else if (ctx->REDUCTION_NOR()) {
    addVObject((antlr4::ParserRuleContext *)ctx->REDUCTION_NOR(),
               VObjectType::slUnary_ReductNor);
  } else if (ctx->REDUCTION_XNOR1()) {
    if (ctx->expression().size() == 1)
      addVObject((antlr4::ParserRuleContext *)ctx->REDUCTION_XNOR1(),
                 VObjectType::slUnary_ReductXnor1);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->REDUCTION_XNOR1(),
                 VObjectType::slBinOp_ReductXnor1);
  } else if (ctx->REDUCTION_XNOR2()) {
    if (ctx->expression().size() == 1)
      addVObject((antlr4::ParserRuleContext *)ctx->REDUCTION_XNOR2(),
                 VObjectType::slUnary_ReductXnor2);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->REDUCTION_XNOR2(),
                 VObjectType::slBinOp_ReductXnor2);
  } else if (ctx->STARSTAR()) {
    addVObject((antlr4::ParserRuleContext *)ctx->STARSTAR(),
               VObjectType::slBinOp_MultMult);
  } else if (ctx->STAR()) {
    addVObject((antlr4::ParserRuleContext *)ctx->STAR(),
               VObjectType::slBinOp_Mult);
  } else if (ctx->DIV()) {
    addVObject((antlr4::ParserRuleContext *)ctx->DIV(),
               VObjectType::slBinOp_Div);
  } else if (ctx->PERCENT()) {
    addVObject((antlr4::ParserRuleContext *)ctx->PERCENT(),
               VObjectType::slBinOp_Percent);
  } else if (ctx->SHIFT_RIGHT()) {
    addVObject((antlr4::ParserRuleContext *)ctx->SHIFT_RIGHT(),
               VObjectType::slBinOp_ShiftRight);
  } else if (ctx->SHIFT_LEFT()) {
    addVObject((antlr4::ParserRuleContext *)ctx->SHIFT_LEFT(),
               VObjectType::slBinOp_ShiftLeft);
  } else if (ctx->ARITH_SHIFT_RIGHT()) {
    addVObject((antlr4::ParserRuleContext *)ctx->ARITH_SHIFT_RIGHT(),
               VObjectType::slBinOp_ArithShiftRight);
  } else if (ctx->ARITH_SHIFT_LEFT()) {
    addVObject((antlr4::ParserRuleContext *)ctx->ARITH_SHIFT_LEFT(),
               VObjectType::slBinOp_ArithShiftLeft);
  } else if (ctx->LESS()) {
    addVObject((antlr4::ParserRuleContext *)ctx->LESS(),
               VObjectType::slBinOp_Less);
  } else if (ctx->LESS_EQUAL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->LESS_EQUAL(),
               VObjectType::slBinOp_LessEqual);
  } else if (ctx->PLUSPLUS()) {
    addVObject((antlr4::ParserRuleContext *)ctx->PLUSPLUS(),
               VObjectType::slIncDec_PlusPlus);
  } else if (ctx->MINUSMINUS()) {
    addVObject((antlr4::ParserRuleContext *)ctx->MINUSMINUS(),
               VObjectType::slIncDec_MinusMinus);
  } else if (ctx->GREATER()) {
    addVObject((antlr4::ParserRuleContext *)ctx->GREATER(),
               VObjectType::slBinOp_Great);
  } else if (ctx->GREATER_EQUAL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->GREATER_EQUAL(),
               VObjectType::slBinOp_GreatEqual);
  } else if (ctx->INSIDE()) {
    addVObject((antlr4::ParserRuleContext *)ctx->INSIDE(),
               VObjectType::slInsideOp);
  } else if (ctx->EQUIV()) {
    addVObject((antlr4::ParserRuleContext *)ctx->EQUIV(),
               VObjectType::slBinOp_Equiv);
  } else if (ctx->NOTEQUAL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->NOTEQUAL(),
               VObjectType::slBinOp_Not);
  } else if (ctx->BINARY_WILDCARD_EQUAL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->BINARY_WILDCARD_EQUAL(),
               VObjectType::slBinOp_WildcardEqual);
  } else if (ctx->BINARY_WILDCARD_NOTEQUAL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->BINARY_WILDCARD_NOTEQUAL(),
               VObjectType::slBinOp_WildcardNotEqual);
  } else if (ctx->FOUR_STATE_LOGIC_EQUAL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->FOUR_STATE_LOGIC_EQUAL(),
               VObjectType::slBinOp_FourStateLogicEqual);
  } else if (ctx->FOUR_STATE_LOGIC_NOTEQUAL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->FOUR_STATE_LOGIC_NOTEQUAL(),
               VObjectType::slBinOp_FourStateLogicNotEqual);
  } else if (ctx->WILD_EQUAL_OP()) {
    addVObject((antlr4::ParserRuleContext *)ctx->WILD_EQUAL_OP(),
               VObjectType::slBinOp_WildEqual);
  } else if (ctx->WILD_NOTEQUAL_OP()) {
    addVObject((antlr4::ParserRuleContext *)ctx->WILD_NOTEQUAL_OP(),
               VObjectType::slBinOp_WildEqual);
  } else if (ctx->BITW_AND()) {
    if (ctx->expression().size() == 1)
      addVObject((antlr4::ParserRuleContext *)ctx->BITW_AND(),
                 VObjectType::slUnary_BitwAnd);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->BITW_AND(),
                 VObjectType::slBinOp_BitwAnd);
  } else if (ctx->LOGICAL_AND().size()) {
    addVObject((antlr4::ParserRuleContext *)ctx->LOGICAL_AND()[0],
               VObjectType::slBinOp_LogicAnd);
  } else if (ctx->LOGICAL_OR()) {
    addVObject((antlr4::ParserRuleContext *)ctx->LOGICAL_OR(),
               VObjectType::slBinOp_LogicOr);
  } else if (ctx->IMPLY()) {
    addVObject((antlr4::ParserRuleContext *)ctx->IMPLY(),
               VObjectType::slBinOp_Imply);
  } else if (ctx->EQUIVALENCE()) {
    addVObject((antlr4::ParserRuleContext *)ctx->EQUIVALENCE(),
               VObjectType::slBinOp_Equivalence);
  } else if (ctx->TAGGED()) {
    addVObject((antlr4::ParserRuleContext *)ctx->TAGGED(),
               VObjectType::slTagged);
  }
  if (ctx->QMARK()) {
    addVObject((antlr4::ParserRuleContext *)ctx->QMARK(), VObjectType::slQmark);
  }
  addVObject(ctx, VObjectType::slExpression);
}

void SV3_1aTreeShapeListener::exitEvent_expression(
    SV3_1aParser::Event_expressionContext *ctx) {
  if (ctx->IFF()) {
    addVObject((antlr4::ParserRuleContext *)ctx->IFF(), VObjectType::slIff);
  }
  addVObject(ctx, VObjectType::slEvent_expression);
}

void SV3_1aTreeShapeListener::exitConstant_expression(
    SV3_1aParser::Constant_expressionContext *ctx) {
  if (ctx->PLUS()) {
    if (ctx->constant_primary())
      addVObject((antlr4::ParserRuleContext *)ctx->PLUS(),
                 VObjectType::slUnary_Plus);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->PLUS(),
                 VObjectType::slBinOp_Plus);
  } else if (ctx->MINUS()) {
    if (ctx->constant_primary())
      addVObject((antlr4::ParserRuleContext *)ctx->MINUS(),
                 VObjectType::slUnary_Minus);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->MINUS(),
                 VObjectType::slBinOp_Minus);
  } else if (ctx->BANG()) {
    addVObject((antlr4::ParserRuleContext *)ctx->BANG(),
               VObjectType::slUnary_Not);
  } else if (ctx->TILDA()) {
    addVObject((antlr4::ParserRuleContext *)ctx->TILDA(),
               VObjectType::slUnary_Tilda);
  } else if (ctx->BITW_AND()) {
    if (ctx->constant_primary())
      addVObject((antlr4::ParserRuleContext *)ctx->BITW_AND(),
                 VObjectType::slUnary_BitwAnd);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->BITW_AND(),
                 VObjectType::slBinOp_BitwAnd);
  } else if (ctx->BITW_OR()) {
    if (ctx->constant_primary())
      addVObject((antlr4::ParserRuleContext *)ctx->BITW_OR(),
                 VObjectType::slUnary_BitwOr);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->BITW_OR(),
                 VObjectType::slBinOp_BitwOr);
  } else if (ctx->BITW_XOR()) {
    if (ctx->constant_primary())
      addVObject((antlr4::ParserRuleContext *)ctx->BITW_XOR(),
                 VObjectType::slUnary_BitwXor);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->BITW_XOR(),
                 VObjectType::slBinOp_BitwXor);
  } else if (ctx->REDUCTION_NAND()) {
    if (ctx->constant_primary())
      addVObject((antlr4::ParserRuleContext *)ctx->REDUCTION_NAND(),
                 VObjectType::slUnary_ReductNand);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->REDUCTION_NAND(),
                 VObjectType::slBinOp_ReductNand);
  } else if (ctx->REDUCTION_NOR()) {
    addVObject((antlr4::ParserRuleContext *)ctx->REDUCTION_NOR(),
               VObjectType::slUnary_ReductNor);
  } else if (ctx->REDUCTION_XNOR1()) {
    if (ctx->constant_primary())
      addVObject((antlr4::ParserRuleContext *)ctx->REDUCTION_XNOR1(),
                 VObjectType::slUnary_ReductXnor1);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->REDUCTION_XNOR1(),
                 VObjectType::slBinOp_ReductXnor1);
  } else if (ctx->REDUCTION_XNOR2()) {
    if (ctx->constant_primary())
      addVObject((antlr4::ParserRuleContext *)ctx->REDUCTION_XNOR2(),
                 VObjectType::slUnary_ReductXnor2);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->REDUCTION_XNOR2(),
                 VObjectType::slBinOp_ReductXnor2);
  } else if (ctx->STARSTAR()) {
    addVObject((antlr4::ParserRuleContext *)ctx->STARSTAR(),
               VObjectType::slBinOp_MultMult);
  } else if (ctx->STAR()) {
    addVObject((antlr4::ParserRuleContext *)ctx->STAR(),
               VObjectType::slBinOp_Mult);
  } else if (ctx->DIV()) {
    addVObject((antlr4::ParserRuleContext *)ctx->DIV(),
               VObjectType::slBinOp_Div);
  } else if (ctx->PERCENT()) {
    addVObject((antlr4::ParserRuleContext *)ctx->PERCENT(),
               VObjectType::slBinOp_Percent);
  } else if (ctx->SHIFT_RIGHT()) {
    addVObject((antlr4::ParserRuleContext *)ctx->SHIFT_RIGHT(),
               VObjectType::slBinOp_ShiftRight);
  } else if (ctx->SHIFT_LEFT()) {
    addVObject((antlr4::ParserRuleContext *)ctx->SHIFT_LEFT(),
               VObjectType::slBinOp_ShiftLeft);
  } else if (ctx->ARITH_SHIFT_RIGHT()) {
    addVObject((antlr4::ParserRuleContext *)ctx->ARITH_SHIFT_RIGHT(),
               VObjectType::slBinOp_ArithShiftRight);
  } else if (ctx->ARITH_SHIFT_LEFT()) {
    addVObject((antlr4::ParserRuleContext *)ctx->ARITH_SHIFT_LEFT(),
               VObjectType::slBinOp_ArithShiftLeft);
  } else if (ctx->LESS()) {
    addVObject((antlr4::ParserRuleContext *)ctx->LESS(),
               VObjectType::slBinOp_Less);
  } else if (ctx->LESS_EQUAL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->LESS_EQUAL(),
               VObjectType::slBinOp_LessEqual);
  } else if (ctx->GREATER()) {
    addVObject((antlr4::ParserRuleContext *)ctx->GREATER(),
               VObjectType::slBinOp_Great);
  } else if (ctx->GREATER_EQUAL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->GREATER_EQUAL(),
               VObjectType::slBinOp_GreatEqual);
  } else if (ctx->INSIDE()) {
    addVObject((antlr4::ParserRuleContext *)ctx->INSIDE(),
               VObjectType::slInsideOp);
  } else if (ctx->EQUIV()) {
    addVObject((antlr4::ParserRuleContext *)ctx->EQUIV(),
               VObjectType::slBinOp_Equiv);
  } else if (ctx->NOTEQUAL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->NOTEQUAL(),
               VObjectType::slBinOp_Not);
  } else if (ctx->BINARY_WILDCARD_EQUAL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->BINARY_WILDCARD_EQUAL(),
               VObjectType::slBinOp_WildcardEqual);
  } else if (ctx->BINARY_WILDCARD_NOTEQUAL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->BINARY_WILDCARD_NOTEQUAL(),
               VObjectType::slBinOp_WildcardNotEqual);
  } else if (ctx->FOUR_STATE_LOGIC_EQUAL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->FOUR_STATE_LOGIC_EQUAL(),
               VObjectType::slBinOp_FourStateLogicEqual);
  } else if (ctx->FOUR_STATE_LOGIC_NOTEQUAL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->FOUR_STATE_LOGIC_NOTEQUAL(),
               VObjectType::slBinOp_FourStateLogicNotEqual);
  } else if (ctx->WILD_EQUAL_OP()) {
    addVObject((antlr4::ParserRuleContext *)ctx->WILD_EQUAL_OP(),
               VObjectType::slBinOp_WildEqual);
  } else if (ctx->WILD_NOTEQUAL_OP()) {
    addVObject((antlr4::ParserRuleContext *)ctx->WILD_NOTEQUAL_OP(),
               VObjectType::slBinOp_WildEqual);
  } else if (ctx->BITW_AND()) {
    if (ctx->constant_primary())
      addVObject((antlr4::ParserRuleContext *)ctx->BITW_AND(),
                 VObjectType::slUnary_BitwAnd);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->BITW_AND(),
                 VObjectType::slBinOp_BitwAnd);
  } else if (ctx->LOGICAL_AND().size()) {
    addVObject((antlr4::ParserRuleContext *)ctx->LOGICAL_AND()[0],
               VObjectType::slBinOp_LogicAnd);
  } else if (ctx->LOGICAL_OR()) {
    addVObject((antlr4::ParserRuleContext *)ctx->LOGICAL_OR(),
               VObjectType::slBinOp_LogicOr);
  } else if (ctx->IMPLY()) {
    addVObject((antlr4::ParserRuleContext *)ctx->IMPLY(),
               VObjectType::slBinOp_Imply);
  } else if (ctx->EQUIVALENCE()) {
    addVObject((antlr4::ParserRuleContext *)ctx->EQUIVALENCE(),
               VObjectType::slBinOp_Equivalence);
  }
  addVObject(ctx, VObjectType::slConstant_expression);
}

void SV3_1aTreeShapeListener::exitNet_type(SV3_1aParser::Net_typeContext *ctx) {
  if (ctx->SUPPLY0()) {
    addVObject(ctx, VObjectType::slNetType_Supply0);
  } else if (ctx->SUPPLY1()) {
    addVObject(ctx, VObjectType::slNetType_Supply1);
  } else if (ctx->TRI()) {
    addVObject(ctx, VObjectType::slNetType_Tri);
  } else if (ctx->TRIAND()) {
    addVObject(ctx, VObjectType::slNetType_TriAnd);
  } else if (ctx->TRIOR()) {
    addVObject(ctx, VObjectType::slNetType_TriOr);
  } else if (ctx->TRIREG()) {
    addVObject(ctx, VObjectType::slNetType_TriReg);
  } else if (ctx->TRI0()) {
    addVObject(ctx, VObjectType::slNetType_Tri0);
  } else if (ctx->TRI1()) {
    addVObject(ctx, VObjectType::slNetType_Tri1);
  } else if (ctx->UWIRE()) {
    addVObject(ctx, VObjectType::slNetType_Uwire);
  } else if (ctx->WIRE()) {
    addVObject(ctx, VObjectType::slNetType_Wire);
  } else if (ctx->WAND()) {
    addVObject(ctx, VObjectType::slNetType_Wand);
  } else if (ctx->WOR()) {
    addVObject(ctx, VObjectType::slNetType_Wor);
  }
}

void SV3_1aTreeShapeListener::exitAssignment_operator(
    SV3_1aParser::Assignment_operatorContext *ctx) {
  if (ctx->ASSIGN_OP()) {
    addVObject(ctx, VObjectType::slAssignOp_Assign);
  } else if (ctx->ADD_ASSIGN()) {
    addVObject(ctx, VObjectType::slAssignOp_Add);
  } else if (ctx->SUB_ASSIGN()) {
    addVObject(ctx, VObjectType::slAssignOp_Sub);
  } else if (ctx->MULT_ASSIGN()) {
    addVObject(ctx, VObjectType::slAssignOp_Mult);
  } else if (ctx->DIV_ASSIGN()) {
    addVObject(ctx, VObjectType::slAssignOp_Div);
  } else if (ctx->MODULO_ASSIGN()) {
    addVObject(ctx, VObjectType::slAssignOp_Modulo);
  } else if (ctx->BITW_AND_ASSIGN()) {
    addVObject(ctx, VObjectType::slAssignOp_BitwAnd);
  } else if (ctx->BITW_OR_ASSIGN()) {
    addVObject(ctx, VObjectType::slAssignOp_BitwOr);
  } else if (ctx->BITW_XOR_ASSIGN()) {
    addVObject(ctx, VObjectType::slAssignOp_BitwXor);
  } else if (ctx->BITW_LEFT_SHIFT_ASSIGN()) {
    addVObject(ctx, VObjectType::slAssignOp_BitwLeftShift);
  } else if (ctx->BITW_RIGHT_SHIFT_ASSIGN()) {
    addVObject(ctx, VObjectType::slAssignOp_BitwRightShift);
  } else if (ctx->ARITH_SHIFT_LEFT_ASSIGN()) {
    addVObject(ctx, VObjectType::slAssignOp_ArithShiftLeft);
  } else if (ctx->ARITH_SHIFT_RIGHT_ASSIGN()) {
    addVObject(ctx, VObjectType::slAssignOp_ArithShiftRight);
  }
}

void SV3_1aTreeShapeListener::exitInc_or_dec_operator(
    SV3_1aParser::Inc_or_dec_operatorContext *ctx) {
  if (ctx->PLUSPLUS())
    addVObject(ctx, VObjectType::slIncDec_PlusPlus);
  else
    addVObject(ctx, VObjectType::slIncDec_MinusMinus);
}

void SV3_1aTreeShapeListener::exitGate_instantiation(
    SV3_1aParser::Gate_instantiationContext *ctx) {
  if (ctx->PULLUP()) {
    addVObject((antlr4::ParserRuleContext *)ctx->PULLUP(),
               VObjectType::slPullup);
  } else if (ctx->PULLDOWN()) {
    addVObject((antlr4::ParserRuleContext *)ctx->PULLDOWN(),
               VObjectType::slPulldown);
  }
  addVObject(ctx, VObjectType::slGate_instantiation);
}

void SV3_1aTreeShapeListener::exitOutput_symbol(
    SV3_1aParser::Output_symbolContext *ctx) {
  if (ctx->Integral_number()) {
    auto number = ctx->Integral_number();
    addVObject((antlr4::ParserRuleContext *)ctx->Integral_number(),
               number->getText(), VObjectType::slIntConst);
  } else if (ctx->Simple_identifier()) {
    std::string ident = ctx->Simple_identifier()->getText();
    addVObject((antlr4::ParserRuleContext *)ctx->Simple_identifier(), ident,
               VObjectType::slStringConst);
  }
  addVObject(ctx, VObjectType::slOutput_symbol);
}

void SV3_1aTreeShapeListener::exitCycle_delay(
    SV3_1aParser::Cycle_delayContext *ctx) {
  if (ctx->Integral_number()) {
    auto number = ctx->Integral_number();
    addVObject((antlr4::ParserRuleContext *)ctx->Integral_number(),
               number->getText(), VObjectType::slIntConst);
  }
  if (ctx->Pound_Pound_delay()) {
    addVObject((antlr4::ParserRuleContext *)ctx->Pound_Pound_delay(),
               ctx->Pound_Pound_delay()->getText(),
               VObjectType::slPound_Pound_delay);
  }
  addVObject(ctx, VObjectType::slCycle_delay);
}

void SV3_1aTreeShapeListener::exitCycle_delay_range(
    SV3_1aParser::Cycle_delay_rangeContext *ctx) {
  if (ctx->Pound_Pound_delay()) {
    addVObject((antlr4::ParserRuleContext *)ctx->Pound_Pound_delay(),
               ctx->Pound_Pound_delay()->getText(),
               VObjectType::slPound_Pound_delay);
  }
  if (ctx->POUNDPOUND()) {
    addVObject((antlr4::ParserRuleContext *)ctx->POUNDPOUND(),
               ctx->POUNDPOUND()->getText(), VObjectType::slPound_Pound_delay);
  }
  if (ctx->PLUS()) {
    addVObject((antlr4::ParserRuleContext *)ctx->PLUS(),
               VObjectType::slUnary_Plus);
  }
  if (ctx->ASSOCIATIVE_UNSPECIFIED()) {
    addVObject((antlr4::ParserRuleContext *)ctx->ASSOCIATIVE_UNSPECIFIED(),
               VObjectType::slAssociative_dimension);
  }
  addVObject(ctx, VObjectType::slCycle_delay_range);
}

void SV3_1aTreeShapeListener::exitSequence_expr(
    SV3_1aParser::Sequence_exprContext *ctx) {
  if (ctx->WITHIN()) {
    addVObject((antlr4::ParserRuleContext *)ctx->WITHIN(),
               VObjectType::slWithin);
  }
  if (ctx->THROUGHOUT()) {
    addVObject((antlr4::ParserRuleContext *)ctx->THROUGHOUT(),
               VObjectType::slThroughout);
  }
  if (ctx->FIRST_MATCH()) {
    addVObject((antlr4::ParserRuleContext *)ctx->FIRST_MATCH(),
               VObjectType::slFirstMatch);
  }
  if (ctx->INTERSECT()) {
    addVObject((antlr4::ParserRuleContext *)ctx->INTERSECT(),
               VObjectType::slIntersect);
  }
  addVObject(ctx, VObjectType::slSequence_expr);
}

void SV3_1aTreeShapeListener::exitLevel_symbol(
    SV3_1aParser::Level_symbolContext *ctx) {
  if (ctx->Integral_number()) {
    auto number = ctx->Integral_number();
    addVObject((antlr4::ParserRuleContext *)ctx->Integral_number(),
               number->getText(), VObjectType::slIntConst);
  } else if (ctx->Simple_identifier()) {
    std::string ident = ctx->Simple_identifier()->getText();
    addVObject((antlr4::ParserRuleContext *)ctx->Simple_identifier(), ident,
               VObjectType::slStringConst);
  } else if (ctx->QMARK()) {
    addVObject((antlr4::ParserRuleContext *)ctx->QMARK(), VObjectType::slQmark);
  }
  addVObject(ctx, VObjectType::slLevel_symbol);
}

void SV3_1aTreeShapeListener::exitEdge_symbol(
    SV3_1aParser::Edge_symbolContext *ctx) {
  if (ctx->Simple_identifier()) {
    std::string ident = ctx->Simple_identifier()->getText();
    addVObject((antlr4::ParserRuleContext *)ctx->Simple_identifier(), ident,
               VObjectType::slStringConst);
  } else if (ctx->STAR()) {
    addVObject((antlr4::ParserRuleContext *)ctx->STAR(),
               VObjectType::slBinOp_Mult);
  }
  addVObject(ctx, VObjectType::slEdge_symbol);
}

void SV3_1aTreeShapeListener::enterUnconnected_drive_directive(
    SV3_1aParser::Unconnected_drive_directiveContext *ctx) {
  if (ctx->Simple_identifier()) {
    std::string text = ctx->Simple_identifier()->getText();
    logError(ErrorDefinition::PA_UNCONNECTED_DRIVE_VALUE, ctx, text);
  }
}

void SV3_1aTreeShapeListener::enterNounconnected_drive_directive(
    SV3_1aParser::Nounconnected_drive_directiveContext *ctx) {}

void SV3_1aTreeShapeListener::enterEveryRule(antlr4::ParserRuleContext *ctx) {}
void SV3_1aTreeShapeListener::exitEveryRule(antlr4::ParserRuleContext *ctx) {}
void SV3_1aTreeShapeListener::visitTerminal(antlr4::tree::TerminalNode *node) {}
void SV3_1aTreeShapeListener::visitErrorNode(antlr4::tree::ErrorNode *node) {}

void SV3_1aTreeShapeListener::exitBegin_keywords_directive(
    SV3_1aParser::Begin_keywords_directiveContext *ctx) {}

void SV3_1aTreeShapeListener::exitEnd_keywords_directive(
    SV3_1aParser::End_keywords_directiveContext *ctx) {}

void SV3_1aTreeShapeListener::exitRandomize_call(
    SV3_1aParser::Randomize_callContext *ctx) {
  if (ctx->NULL_KEYWORD()) {
    addVObject((antlr4::ParserRuleContext *)ctx->NULL_KEYWORD(),
               VObjectType::slNull);
  }
  if (ctx->WITH()) {
    addVObject((antlr4::ParserRuleContext *)ctx->WITH(), VObjectType::slWith);
  }
  addVObject(ctx, VObjectType::slRandomize_call);
}

void SV3_1aTreeShapeListener::exitDeferred_immediate_assert_statement(
    SV3_1aParser::Deferred_immediate_assert_statementContext *ctx) {
  if (ctx->Pound_delay()) {
    addVObject((antlr4::ParserRuleContext *)ctx->Pound_delay(),
               ctx->Pound_delay()->getText(), VObjectType::slPound_delay);
  } else if (ctx->Pound_Pound_delay()) {
    addVObject((antlr4::ParserRuleContext *)ctx->Pound_Pound_delay(),
               ctx->Pound_Pound_delay()->getText(),
               VObjectType::slPound_Pound_delay);
  }
  addVObject(ctx, VObjectType::slDeferred_immediate_assert_statement);
}

void SV3_1aTreeShapeListener::exitDeferred_immediate_assume_statement(
    SV3_1aParser::Deferred_immediate_assume_statementContext *ctx) {
  if (ctx->Pound_delay()) {
    addVObject((antlr4::ParserRuleContext *)ctx->Pound_delay(),
               ctx->Pound_delay()->getText(), VObjectType::slPound_delay);
  } else if (ctx->Pound_Pound_delay()) {
    addVObject((antlr4::ParserRuleContext *)ctx->Pound_Pound_delay(),
               ctx->Pound_Pound_delay()->getText(),
               VObjectType::slPound_Pound_delay);
  }
  addVObject(ctx, VObjectType::slDeferred_immediate_assume_statement);
}

void SV3_1aTreeShapeListener::exitDeferred_immediate_cover_statement(
    SV3_1aParser::Deferred_immediate_cover_statementContext *ctx) {
  if (ctx->Pound_delay()) {
    addVObject((antlr4::ParserRuleContext *)ctx->Pound_delay(),
               ctx->Pound_delay()->getText(), VObjectType::slPound_delay);
  } else if (ctx->Pound_Pound_delay()) {
    addVObject((antlr4::ParserRuleContext *)ctx->Pound_Pound_delay(),
               ctx->Pound_Pound_delay()->getText(),
               VObjectType::slPound_Pound_delay);
  }
  addVObject(ctx, VObjectType::slDeferred_immediate_cover_statement);
}

void SV3_1aTreeShapeListener::exitLocal_parameter_declaration(
    SV3_1aParser::Local_parameter_declarationContext *ctx) {
  if (ctx->TYPE()) {
    addVObject((antlr4::ParserRuleContext *)ctx->TYPE(), VObjectType::slType);
  }
  addVObject(ctx, VObjectType::slLocal_parameter_declaration);
}

void SV3_1aTreeShapeListener::exitParameter_declaration(
    SV3_1aParser::Parameter_declarationContext *ctx) {
  if (ctx->TYPE()) {
    addVObject((antlr4::ParserRuleContext *)ctx->TYPE(), VObjectType::slType);
  }
  addVObject(ctx, VObjectType::slParameter_declaration);
}

void SV3_1aTreeShapeListener::exitPort_direction(
    SV3_1aParser::Port_directionContext *ctx) {
  if (ctx->INPUT()) {
    addVObject(ctx, VObjectType::slPortDir_Inp);
  } else if (ctx->OUTPUT()) {
    addVObject(ctx, VObjectType::slPortDir_Out);
  } else if (ctx->INOUT()) {
    addVObject(ctx, VObjectType::slPortDir_Inout);
  } else if (ctx->REF()) {
    addVObject(ctx, VObjectType::slPortDir_Ref);
  }
}

void SV3_1aTreeShapeListener::exitInteger_atom_type(
    SV3_1aParser::Integer_atom_typeContext *ctx) {
  if (ctx->INT())
    addVObject(ctx, VObjectType::slIntegerAtomType_Int);
  else if (ctx->BYTE())
    addVObject(ctx, VObjectType::slIntegerAtomType_Byte);
  else if (ctx->SHORTINT())
    addVObject(ctx, VObjectType::slIntegerAtomType_Shortint);
  else if (ctx->LONGINT())
    addVObject(ctx, VObjectType::slIntegerAtomType_LongInt);
  else if (ctx->INTEGER())
    addVObject(ctx, VObjectType::slIntegerAtomType_Int);
  else if (ctx->TIME())
    addVObject(ctx, VObjectType::slIntegerAtomType_Time);
}

void SV3_1aTreeShapeListener::exitInteger_vector_type(
    SV3_1aParser::Integer_vector_typeContext *ctx) {
  if (ctx->LOGIC())
    addVObject(ctx, VObjectType::slIntVec_TypeLogic);
  else if (ctx->REG())
    addVObject(ctx, VObjectType::slIntVec_TypeReg);
  else if (ctx->BIT())
    addVObject(ctx, VObjectType::slIntVec_TypeBit);
}

void SV3_1aTreeShapeListener::exitNon_integer_type(
    SV3_1aParser::Non_integer_typeContext *ctx) {
  if (ctx->SHORTREAL())
    addVObject(ctx, VObjectType::slNonIntType_ShortReal);
  else if (ctx->REAL())
    addVObject(ctx, VObjectType::slNonIntType_Real);
  else if (ctx->REALTIME())
    addVObject(ctx, VObjectType::slNonIntType_RealTime);
}

void SV3_1aTreeShapeListener::exitAlways_keyword(
    SV3_1aParser::Always_keywordContext *ctx) {
  if (ctx->ALWAYS_COMB()) {
    addVObject(ctx, VObjectType::slAlwaysKeywd_Comb);
  } else if (ctx->ALWAYS_FF()) {
    addVObject(ctx, VObjectType::slAlwaysKeywd_FF);
  } else if (ctx->ALWAYS_LATCH()) {
    addVObject(ctx, VObjectType::slAlwaysKeywd_Latch);
  } else if (ctx->ALWAYS()) {
    addVObject(ctx, VObjectType::slAlwaysKeywd_Always);
  }
}

void SV3_1aTreeShapeListener::exitEdge_identifier(
    SV3_1aParser::Edge_identifierContext *ctx) {
  if (ctx->POSEDGE())
    addVObject(ctx, VObjectType::slEdge_Posedge);
  else if (ctx->NEGEDGE())
    addVObject(ctx, VObjectType::slEdge_Negedge);
  else if (ctx->EDGE())
    addVObject(ctx, VObjectType::slEdge_Edge);
}

void SV3_1aTreeShapeListener::exitNumber(SV3_1aParser::NumberContext *ctx) {
  if (ctx->Integral_number()) {
    auto number = ctx->Integral_number();
    addVObject(ctx, number->getText(), VObjectType::slIntConst);
  } else if (ctx->Real_number())
    addVObject(ctx, ctx->Real_number()->getText(), VObjectType::slRealConst);
  else if (ctx->ONE_TICK_b0())
    addVObject(ctx, VObjectType::slNumber_1Tickb0);
  else if (ctx->ONE_TICK_b1())
    addVObject(ctx, VObjectType::slNumber_1Tickb1);
  else if (ctx->ONE_TICK_B0())
    addVObject(ctx, VObjectType::slNumber_1TickB0);
  else if (ctx->ONE_TICK_B1())
    addVObject(ctx, VObjectType::slNumber_1TickB1);
  else if (ctx->TICK_b0())
    addVObject(ctx, VObjectType::slNumber_Tickb0);
  else if (ctx->TICK_b1())
    addVObject(ctx, VObjectType::slNumber_Tickb1);
  else if (ctx->TICK_B0())
    addVObject(ctx, VObjectType::slNumber_TickB0);
  else if (ctx->TICK_B1())
    addVObject(ctx, VObjectType::slNumber_TickB1);
  else if (ctx->TICK_0())
    addVObject(ctx, VObjectType::slNumber_Tick0);
  else if (ctx->TICK_1())
    addVObject(ctx, VObjectType::slNumber_Tick1);
  else if (ctx->ONE_TICK_bx())
    addVObject(ctx, VObjectType::slNumber_1Tickbx);
  else if (ctx->ONE_TICK_bX())
    addVObject(ctx, VObjectType::slNumber_1TickbX);
  else if (ctx->ONE_TICK_Bx())
    addVObject(ctx, VObjectType::slNumber_1TickBx);
  else if (ctx->ONE_TICK_BX())
    addVObject(ctx, VObjectType::slNumber_1TickbX);
}

void SV3_1aTreeShapeListener::exitSigning(SV3_1aParser::SigningContext *ctx) {
  if (ctx->SIGNED())
    addVObject(ctx, VObjectType::slSigning_Signed);
  else if (ctx->UNSIGNED())
    addVObject(ctx, VObjectType::slSigning_Unsigned);
}

void SV3_1aTreeShapeListener::exitTf_port_direction(
    SV3_1aParser::Tf_port_directionContext *ctx) {
  if (ctx->INPUT())
    addVObject(ctx, VObjectType::slTfPortDir_Inp);
  else if (ctx->OUTPUT())
    addVObject(ctx, VObjectType::slTfPortDir_Out);
  else if (ctx->INOUT())
    addVObject(ctx, VObjectType::slTfPortDir_Inout);
  else if (ctx->REF())
    addVObject(ctx, VObjectType::slTfPortDir_Ref);
  else if (ctx->CONST())
    addVObject(ctx, VObjectType::slTfPortDir_ConstRef);
}

void SV3_1aTreeShapeListener::exitDefault_nettype_directive(
    SV3_1aParser::Default_nettype_directiveContext *ctx) {
  NetTypeInfo info;
  info.m_type = slNetType_Wire;
  info.m_fileId = m_pf->getFileId(0);
  std::pair<int, int> lineCol = ParseUtils::getLineColumn(m_tokens, ctx);
  info.m_line = lineCol.first;
  if (ctx->Simple_identifier()) {
    addVObject((antlr4::ParserRuleContext *)ctx->Simple_identifier(),
               ctx->Simple_identifier()->getText(), VObjectType::slStringConst);
    info.m_type = slNoType;
  } else if (ctx->net_type()) {
    if (ctx->net_type()->SUPPLY0())
      info.m_type = slSupply0;
    else if (ctx->net_type()->SUPPLY1())
      info.m_type = slSupply1;
    else if (ctx->net_type()->WIRE())
      info.m_type = slNetType_Wire;
    else if (ctx->net_type()->UWIRE())
      info.m_type = slNetType_Uwire;
    else if (ctx->net_type()->WAND())
      info.m_type = slNetType_Wand;
    else if (ctx->net_type()->WOR())
      info.m_type = slNetType_Wor;
    else if (ctx->net_type()->TRI())
      info.m_type = slNetType_Tri;
    else if (ctx->net_type()->TRIREG())
      info.m_type = slNetType_TriReg;
    else if (ctx->net_type()->TRIOR())
      info.m_type = slNetType_TriOr;
    else if (ctx->net_type()->TRIAND())
      info.m_type = slNetType_TriAnd;
    else if (ctx->net_type()->TRI0())
      info.m_type = slNetType_Tri0;
    else if (ctx->net_type()->TRI1())
      info.m_type = slNetType_Tri1;
  }
  addVObject(ctx, VObjectType::slDefault_nettype_directive);
  m_pf->getCompilationUnit()->recordDefaultNetType(info);
}

}  // namespace SURELOG
