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

#include "Surelog/SourceCompile/SV3_1aTreeShapeListener.h"

#include <regex>
#include <string>

#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Design/Design.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/SourceCompile/CompilationUnit.h"
#include "Surelog/SourceCompile/Compiler.h"
#include "Surelog/SourceCompile/ParseFile.h"
#include "Surelog/SourceCompile/SymbolTable.h"
#include "Surelog/Utils/ParseUtils.h"
#include "Surelog/Utils/StringUtils.h"

namespace SURELOG {

void SV3_1aTreeShapeListener::enterTop_level_rule(
    SV3_1aParser::Top_level_ruleContext * /*ctx*/) {
  if (m_pf->getFileContent() == nullptr) {
    m_fileContent = new FileContent(
        m_pf->getFileId(0), m_pf->getLibrary(),
        m_pf->getCompileSourceFile()->getSymbolTable(),
        m_pf->getCompileSourceFile()->getErrorContainer(), nullptr, BadPathId);
    m_pf->setFileContent(m_fileContent);
    m_pf->getCompileSourceFile()->getCompiler()->getDesign()->addFileContent(
        m_pf->getFileId(0), m_fileContent);
  } else {
    m_fileContent = m_pf->getFileContent();
  }
  CommandLineParser *clp = m_pf->getCompileSourceFile()->getCommandLineParser();
  if ((!clp->parseOnly()) && (!clp->lowMem())) {
    m_includeFileInfo.emplace(IncludeFileInfo::Context::NONE, 1, BadSymbolId,
                              m_pf->getFileId(0), 0, 0, 0, 0,
                              IncludeFileInfo::Action::PUSH);
  }
}

void SV3_1aTreeShapeListener::enterTop_level_library_rule(
    SV3_1aParser::Top_level_library_ruleContext * /*ctx*/) {
  // Visited from Library/SVLibShapeListener.h
  m_fileContent = new FileContent(
      m_pf->getFileId(0), m_pf->getLibrary(), m_pf->getSymbolTable(),
      m_pf->getErrorContainer(), nullptr, BadPathId);
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
                         VObjectType::paMODULE);
}

void SV3_1aTreeShapeListener::exitModule_declaration(
    SV3_1aParser::Module_declarationContext *ctx) {
  if (ctx->ENDMODULE() != nullptr) {
    addVObject((antlr4::ParserRuleContext *)ctx->ENDMODULE(),
               VObjectType::paENDMODULE);
  }
  addVObject(ctx, VObjectType::paModule_declaration);
  m_nestedElements.pop();
}

void SV3_1aTreeShapeListener::exitModule_keyword(
    SV3_1aParser::Module_keywordContext *ctx) {
  if (ctx->MODULE() != nullptr) {
    addVObject(ctx, ctx->MODULE()->getText(), VObjectType::paModule_keyword);
  } else if (ctx->MACROMODULE() != nullptr) {
    addVObject(ctx, ctx->MACROMODULE()->getText(),
               VObjectType::paModule_keyword);
  }
}

void SV3_1aTreeShapeListener::exitClass_constructor_declaration(
    SV3_1aParser::Class_constructor_declarationContext *ctx) {
  if (ctx->ENDFUNCTION())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDFUNCTION(),
               VObjectType::paENDFUNCTION);
  addVObject(ctx, VObjectType::paClass_constructor_declaration);
}

void SV3_1aTreeShapeListener::exitFunction_body_declaration(
    SV3_1aParser::Function_body_declarationContext *ctx) {
  if (ctx->ENDFUNCTION())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDFUNCTION(),
               VObjectType::paENDFUNCTION);
  addVObject(ctx, VObjectType::paFunction_body_declaration);
}

void SV3_1aTreeShapeListener::exitTask_body_declaration(
    SV3_1aParser::Task_body_declarationContext *ctx) {
  if (ctx->ENDTASK())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDTASK(),
               VObjectType::paENDTASK);
  addVObject(ctx, VObjectType::paTask_body_declaration);
}

void SV3_1aTreeShapeListener::exitJump_statement(
    SV3_1aParser::Jump_statementContext *ctx) {
  if (ctx->BREAK()) {
    addVObject((antlr4::ParserRuleContext *)ctx->BREAK(), VObjectType::paBREAK);
  } else if (ctx->CONTINUE()) {
    addVObject((antlr4::ParserRuleContext *)ctx->CONTINUE(),
               VObjectType::paCONTINUE);
  } else if (ctx->RETURN()) {
    addVObject((antlr4::ParserRuleContext *)ctx->RETURN(),
               VObjectType::paRETURN);
  }
  addVObject(ctx, VObjectType::paJump_statement);
}

void SV3_1aTreeShapeListener::exitClass_declaration(
    SV3_1aParser::Class_declarationContext *ctx) {
  if (ctx->CLASS())
    addVObject((antlr4::ParserRuleContext *)ctx->CLASS(), VObjectType::paCLASS);
  if (ctx->VIRTUAL())
    addVObject((antlr4::ParserRuleContext *)ctx->VIRTUAL(),
               VObjectType::paVIRTUAL);
  if (ctx->IMPLEMENTS())
    addVObject((antlr4::ParserRuleContext *)ctx->IMPLEMENTS(),
               VObjectType::paIMPLEMENTS);
  if (ctx->EXTENDS())
    addVObject((antlr4::ParserRuleContext *)ctx->EXTENDS(),
               VObjectType::paEXTENDS);
  if (ctx->ENDCLASS())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDCLASS(),
               VObjectType::paENDCLASS);
  addVObject(ctx, VObjectType::paClass_declaration);
}

void SV3_1aTreeShapeListener::exitInterface_class_declaration(
    SV3_1aParser::Interface_class_declarationContext *ctx) {
  if (ctx->INTERFACE())
    addVObject((antlr4::ParserRuleContext *)ctx->INTERFACE(),
               VObjectType::paINTERFACE);
  if (ctx->EXTENDS())
    addVObject((antlr4::ParserRuleContext *)ctx->EXTENDS(),
               VObjectType::paEXTENDS);
  if (ctx->ENDCLASS())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDCLASS(),
               VObjectType::paENDCLASS);
  addVObject(ctx, VObjectType::paInterface_class_declaration);
}

void SV3_1aTreeShapeListener::exitChecker_declaration(
    SV3_1aParser::Checker_declarationContext *ctx) {
  if (ctx->ENDCHECKER())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDCHECKER(),
               VObjectType::paENDCHECKER);
  addVObject(ctx, VObjectType::paChecker_declaration);
}

void SV3_1aTreeShapeListener::enterSlline(
    SV3_1aParser::SllineContext * /*ctx*/) {}

void SV3_1aTreeShapeListener::exitSlline(SV3_1aParser::SllineContext *ctx) {
  FileSystem *const fileSystem = FileSystem::getInstance();
  uint32_t startLine = std::stoi(ctx->Integral_number()[0]->getText());
  IncludeFileInfo::Action action = static_cast<IncludeFileInfo::Action>(
      std::stoi(ctx->Integral_number()[1]->getText()));
  std::string text(StringUtils::unquoted(ctx->String()->getText()));
  std::vector<std::string_view> parts;
  StringUtils::tokenize(text, "^", parts);
  std::string_view symbol = StringUtils::unquoted(parts[0]);
  std::string_view file = StringUtils::unquoted(parts[1]);

  ParseUtils::LineColumn startLineCol =
      ParseUtils::getLineColumn(m_tokens, ctx);
  ParseUtils::LineColumn endLineCol =
      ParseUtils::getEndLineColumn(m_tokens, ctx);
  if (action == IncludeFileInfo::Action::PUSH) {
    // Push
    m_includeFileInfo.emplace(
        IncludeFileInfo::Context::INCLUDE, startLine,
        m_pf->getSymbolTable()->registerSymbol(symbol),
        fileSystem->toPathId(file, m_pf->getSymbolTable()), startLineCol.first,
        startLineCol.second, endLineCol.first, endLineCol.second,
        IncludeFileInfo::Action::PUSH);
  } else if (action == IncludeFileInfo::Action::POP) {
    // Pop
    if (!m_includeFileInfo.empty()) m_includeFileInfo.pop();
    if (!m_includeFileInfo.empty()) {
      IncludeFileInfo &info = m_includeFileInfo.top();
      info.m_sectionSymbolId = m_pf->getSymbolTable()->registerSymbol(symbol);
      info.m_sectionFileId = fileSystem->toPathId(file, m_pf->getSymbolTable());
      info.m_originalStartLine = startLineCol.first /*+ m_lineOffset */;
      info.m_originalStartColumn = startLineCol.second /*+ m_lineOffset */;
      info.m_sectionStartLine = startLine;
      info.m_action = IncludeFileInfo::Action::POP;
    }
  }
}

void SV3_1aTreeShapeListener::enterInterface_declaration(
    SV3_1aParser::Interface_declarationContext *ctx) {
  std::string ident;
  if (ctx->interface_ansi_header()) {
    ident = ctx->interface_ansi_header()->interface_identifier()->getText();
    if (ctx->interface_ansi_header()->INTERFACE()) {
      addVObject((antlr4::ParserRuleContext *)ctx->interface_ansi_header()
                     ->INTERFACE(),
                 VObjectType::paINTERFACE);
    }
  } else if (ctx->interface_nonansi_header()) {
    ident = ctx->interface_nonansi_header()->interface_identifier()->getText();
    if (ctx->interface_nonansi_header()->INTERFACE()) {
      addVObject((antlr4::ParserRuleContext *)ctx->interface_nonansi_header()
                     ->INTERFACE(),
                 VObjectType::paINTERFACE);
    }
  } else {
    if (ctx->interface_identifier(0))
      ident = ctx->interface_identifier(0)->getText();
    else
      ident = "INTERFACE NAME UNKNOWN";
    if (ctx->INTERFACE()) {
      addVObject((antlr4::ParserRuleContext *)ctx->INTERFACE(),
                 VObjectType::paINTERFACE);
    }
  }
  ident = std::regex_replace(ident, std::regex(EscapeSequence), "");
  addNestedDesignElement(ctx, ident, DesignElement::Interface,
                         VObjectType::paINTERFACE);
}

void SV3_1aTreeShapeListener::exitInterface_declaration(
    SV3_1aParser::Interface_declarationContext *ctx) {
  if (ctx->EXTERN() == nullptr)
    if (ctx->ENDINTERFACE())
      addVObject((antlr4::ParserRuleContext *)ctx->ENDINTERFACE(),
                 VObjectType::paENDINTERFACE);
  addVObject(ctx, VObjectType::paInterface_declaration);
  m_nestedElements.pop();
}

void SV3_1aTreeShapeListener::exitProperty_expr(
    SV3_1aParser::Property_exprContext *ctx) {
  if (ctx->CASE()) {
    addVObject((antlr4::ParserRuleContext *)ctx->CASE(), VObjectType::paCASE);
  }
  if (ctx->ENDCASE()) {
    addVObject((antlr4::ParserRuleContext *)ctx->ENDCASE(),
               VObjectType::paENDCASE);
  } else if (ctx->OR()) {
    addVObject((antlr4::ParserRuleContext *)ctx->OR(), VObjectType::paOR);
  } else if (ctx->AND()) {
    addVObject((antlr4::ParserRuleContext *)ctx->AND(), VObjectType::paAND);
  } else if (ctx->IF()) {
    addVObject((antlr4::ParserRuleContext *)ctx->IF(), VObjectType::paIF);
  } else if (ctx->STRONG()) {
    addVObject((antlr4::ParserRuleContext *)ctx->STRONG(),
               VObjectType::paSTRONG);
  } else if (ctx->WEAK()) {
    addVObject((antlr4::ParserRuleContext *)ctx->WEAK(), VObjectType::paWEAK);
  } else if (ctx->NOT()) {
    addVObject((antlr4::ParserRuleContext *)ctx->NOT(), VObjectType::paNOT);
  } else if (ctx->OVERLAP_IMPLY()) {
    addVObject((antlr4::ParserRuleContext *)ctx->OVERLAP_IMPLY(),
               VObjectType::paOVERLAP_IMPLY);
  } else if (ctx->NON_OVERLAP_IMPLY()) {
    addVObject((antlr4::ParserRuleContext *)ctx->NON_OVERLAP_IMPLY(),
               VObjectType::paNON_OVERLAP_IMPLY);
  } else if (ctx->OVERLAPPED()) {
    addVObject((antlr4::ParserRuleContext *)ctx->OVERLAPPED(),
               VObjectType::paOVERLAPPED);
  } else if (ctx->NONOVERLAPPED()) {
    addVObject((antlr4::ParserRuleContext *)ctx->NONOVERLAPPED(),
               VObjectType::paNONOVERLAPPED);
  } else if (ctx->S_NEXTTIME()) {
    addVObject((antlr4::ParserRuleContext *)ctx->S_NEXTTIME(),
               VObjectType::paS_NEXTTIME);
  } else if (ctx->ALWAYS()) {
    addVObject((antlr4::ParserRuleContext *)ctx->ALWAYS(),
               VObjectType::paALWAYS);
  } else if (ctx->S_ALWAYS()) {
    addVObject((antlr4::ParserRuleContext *)ctx->S_ALWAYS(),
               VObjectType::paS_ALWAYS);
  } else if (ctx->S_EVENTUALLY()) {
    addVObject((antlr4::ParserRuleContext *)ctx->S_EVENTUALLY(),
               VObjectType::paS_EVENTUALLY);
  } else if (ctx->EVENTUALLY()) {
    addVObject((antlr4::ParserRuleContext *)ctx->EVENTUALLY(),
               VObjectType::paEVENTUALLY);
  } else if (ctx->UNTIL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->UNTIL(), VObjectType::paUNTIL);
  } else if (ctx->S_UNTIL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->S_UNTIL(),
               VObjectType::paS_UNTIL);
  } else if (ctx->IMPLIES()) {
    addVObject((antlr4::ParserRuleContext *)ctx->IMPLIES(),
               VObjectType::paIMPLIES);
  } else if (ctx->IFF()) {
    addVObject((antlr4::ParserRuleContext *)ctx->IFF(), VObjectType::paIFF);
  } else if (ctx->ACCEPT_ON()) {
    addVObject((antlr4::ParserRuleContext *)ctx->ACCEPT_ON(),
               VObjectType::paACCEPT_ON);
  } else if (ctx->REJECT_ON()) {
    addVObject((antlr4::ParserRuleContext *)ctx->REJECT_ON(),
               VObjectType::paREJECT_ON);
  } else if (ctx->SYNC_ACCEPT_ON()) {
    addVObject((antlr4::ParserRuleContext *)ctx->SYNC_ACCEPT_ON(),
               VObjectType::paSYNC_ACCEPT_ON);
  } else if (ctx->SYNC_REJECT_ON()) {
    addVObject((antlr4::ParserRuleContext *)ctx->SYNC_REJECT_ON(),
               VObjectType::paSYNC_REJECT_ON);
  }
  addVObject(ctx, VObjectType::paProperty_expr);
}

void SV3_1aTreeShapeListener::exitGenerate_module_case_statement(
    SV3_1aParser::Generate_module_case_statementContext *ctx) {
  if (ctx->ENDCASE())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDCASE(),
               VObjectType::paENDCASE);
  addVObject(ctx, VObjectType::paGenerate_module_case_statement);
}

void SV3_1aTreeShapeListener::exitIf_generate_construct(
    SV3_1aParser::If_generate_constructContext *ctx) {
  if (ctx->IF())
    addVObject((antlr4::ParserRuleContext *)ctx->IF(), VObjectType::paIF);
  if (ctx->ELSE())
    addVObject((antlr4::ParserRuleContext *)ctx->ELSE(), VObjectType::paELSE);
  addVObject(ctx, VObjectType::paIf_generate_construct);
}

void SV3_1aTreeShapeListener::exitGenerate_interface_case_statement(
    SV3_1aParser::Generate_interface_case_statementContext *ctx) {
  if (ctx->ENDCASE())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDCASE(),
               VObjectType::paENDCASE);
  addVObject(ctx, VObjectType::paGenerate_interface_case_statement);
}

void SV3_1aTreeShapeListener::exitCase_generate_construct(
    SV3_1aParser::Case_generate_constructContext *ctx) {
  if (ctx->ENDCASE())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDCASE(),
               VObjectType::paENDCASE);
  addVObject(ctx, VObjectType::paCase_generate_construct);
}

void SV3_1aTreeShapeListener::exitCase_statement(
    SV3_1aParser::Case_statementContext *ctx) {
  if (ctx->ENDCASE())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDCASE(),
               VObjectType::paENDCASE);
  addVObject(ctx, VObjectType::paCase_statement);
}

void SV3_1aTreeShapeListener::exitRandcase_statement(
    SV3_1aParser::Randcase_statementContext *ctx) {
  if (ctx->ENDCASE())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDCASE(),
               VObjectType::paENDCASE);
  addVObject(ctx, VObjectType::paRandcase_statement);
}

void SV3_1aTreeShapeListener::exitRs_case(SV3_1aParser::Rs_caseContext *ctx) {
  if (ctx->ENDCASE())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDCASE(),
               VObjectType::paENDCASE);
  addVObject(ctx, VObjectType::paRs_case);
}

void SV3_1aTreeShapeListener::exitSequence_declaration(
    SV3_1aParser::Sequence_declarationContext *ctx) {
  if (ctx->ENDSEQUENCE())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDSEQUENCE(),
               VObjectType::paENDSEQUENCE);
  addVObject(ctx, VObjectType::paSequence_declaration);
}

void SV3_1aTreeShapeListener::exitRandsequence_statement(
    SV3_1aParser::Randsequence_statementContext *ctx) {
  if (ctx->ENDSEQUENCE())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDSEQUENCE(),
               VObjectType::paENDSEQUENCE);
  addVObject(ctx, VObjectType::paRandsequence_statement);
}

void SV3_1aTreeShapeListener::exitSeq_block(
    SV3_1aParser::Seq_blockContext *ctx) {
  if (ctx->END())
    addVObject((antlr4::ParserRuleContext *)ctx->END(), VObjectType::paEND);
  addVObject(ctx, VObjectType::paSeq_block);
}

void SV3_1aTreeShapeListener::exitGenerate_module_named_block(
    SV3_1aParser::Generate_module_named_blockContext *ctx) {
  if (ctx->END())
    addVObject((antlr4::ParserRuleContext *)ctx->END(), VObjectType::paEND);
  addVObject(ctx, VObjectType::paGenerate_module_named_block);
}

void SV3_1aTreeShapeListener::exitGenerate_module_block(
    SV3_1aParser::Generate_module_blockContext *ctx) {
  if (ctx->END())
    addVObject((antlr4::ParserRuleContext *)ctx->END(), VObjectType::paEND);
  addVObject(ctx, VObjectType::paGenerate_module_block);
}

void SV3_1aTreeShapeListener::exitGenerate_interface_named_block(
    SV3_1aParser::Generate_interface_named_blockContext *ctx) {
  if (ctx->END())
    addVObject((antlr4::ParserRuleContext *)ctx->END(), VObjectType::paEND);
  addVObject(ctx, VObjectType::paGenerate_interface_named_block);
}

void SV3_1aTreeShapeListener::exitGenerate_interface_block(
    SV3_1aParser::Generate_interface_blockContext *ctx) {
  if (ctx->END())
    addVObject((antlr4::ParserRuleContext *)ctx->END(), VObjectType::paEND);
  addVObject(ctx, VObjectType::paGenerate_interface_block);
}

void SV3_1aTreeShapeListener::exitGenerate_begin_end_block(
    SV3_1aParser::Generate_begin_end_blockContext *ctx) {
  if (ctx->END())
    addVObject((antlr4::ParserRuleContext *)ctx->END(), VObjectType::paEND);
  addVObject(ctx, VObjectType::paGenerate_begin_end_block);
}

void SV3_1aTreeShapeListener::exitNamed_port_connection(
    SV3_1aParser::Named_port_connectionContext *ctx) {
  if (ctx->DOTSTAR())
    addVObject((antlr4::ParserRuleContext *)ctx->DOTSTAR(),
               VObjectType::paDOTSTAR);
  if (ctx->OPEN_PARENS())
    addVObject((antlr4::ParserRuleContext *)ctx->OPEN_PARENS(),
               VObjectType::paOPEN_PARENS);
  if (ctx->CLOSE_PARENS())
    addVObject((antlr4::ParserRuleContext *)ctx->CLOSE_PARENS(),
               VObjectType::paCLOSE_PARENS);
  addVObject(ctx, VObjectType::paNamed_port_connection);
}

void SV3_1aTreeShapeListener::exitPattern(SV3_1aParser::PatternContext *ctx) {
  if (ctx->DOT())
    addVObject((antlr4::ParserRuleContext *)ctx->DOT(), VObjectType::paDOT);
  else if (ctx->DOTSTAR())
    addVObject((antlr4::ParserRuleContext *)ctx->DOTSTAR(),
               VObjectType::paDOTSTAR);
  else if (ctx->TAGGED())
    addVObject((antlr4::ParserRuleContext *)ctx->TAGGED(),
               VObjectType::paTAGGED);

  addVObject(ctx, VObjectType::paPattern);
}

void SV3_1aTreeShapeListener::exitSpecify_block(
    SV3_1aParser::Specify_blockContext *ctx) {
  if (ctx->ENDSPECIFY())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDSPECIFY(),
               VObjectType::paENDSPECIFY);
  addVObject(ctx, VObjectType::paSpecify_block);
}

void SV3_1aTreeShapeListener::exitConfig_declaration(
    SV3_1aParser::Config_declarationContext *ctx) {
  if (ctx->ENDCONFIG())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDCONFIG(),
               VObjectType::paENDCONFIG);
  addVObject(ctx, VObjectType::paConfig_declaration);
}

void SV3_1aTreeShapeListener::exitDpi_import_export(
    SV3_1aParser::Dpi_import_exportContext *ctx) {
  if (ctx->IMPORT())
    addVObject((antlr4::ParserRuleContext *)ctx->IMPORT(),
               VObjectType::paIMPORT);
  if (ctx->EXPORT())
    addVObject((antlr4::ParserRuleContext *)ctx->EXPORT(),
               VObjectType::paEXPORT);
  addVObject(ctx, VObjectType::paDpi_import_export);
}

void SV3_1aTreeShapeListener::exitProperty_declaration(
    SV3_1aParser::Property_declarationContext *ctx) {
  if (ctx->ENDPROPERTY())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDPROPERTY(),
               VObjectType::paENDPROPERTY);
  addVObject(ctx, VObjectType::paProperty_declaration);
}

void SV3_1aTreeShapeListener::exitCovergroup_declaration(
    SV3_1aParser::Covergroup_declarationContext *ctx) {
  if (ctx->ENDGROUP())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDGROUP(),
               VObjectType::paENDGROUP);
  addVObject(ctx, VObjectType::paCovergroup_declaration);
}

void SV3_1aTreeShapeListener::exitGenerated_module_instantiation(
    SV3_1aParser::Generated_module_instantiationContext *ctx) {
  if (ctx->ENDGENERATE())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDGENERATE(),
               VObjectType::paENDGENERATE);
  addVObject(ctx, VObjectType::paGenerated_module_instantiation);
}

void SV3_1aTreeShapeListener::exitGenerated_interface_instantiation(
    SV3_1aParser::Generated_interface_instantiationContext *ctx) {
  if (ctx->ENDGENERATE())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDGENERATE(),
               VObjectType::paENDGENERATE);
  addVObject(ctx, VObjectType::paGenerated_interface_instantiation);
}

void SV3_1aTreeShapeListener::exitGenerate_region(
    SV3_1aParser::Generate_regionContext *ctx) {
  if (ctx->ENDGENERATE())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDGENERATE(),
               VObjectType::paENDGENERATE);
  addVObject(ctx, VObjectType::paGenerate_region);
}

void SV3_1aTreeShapeListener::exitUdp_declaration(
    SV3_1aParser::Udp_declarationContext *ctx) {
  if (ctx->ENDPRIMITIVE())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDPRIMITIVE(),
               VObjectType::paENDPRIMITIVE);
  addVObject(ctx, VObjectType::paUdp_declaration);
}

void SV3_1aTreeShapeListener::exitCombinational_body(
    SV3_1aParser::Combinational_bodyContext *ctx) {
  if (ctx->ENDTABLE())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDTABLE(),
               VObjectType::paENDTABLE);
  addVObject(ctx, VObjectType::paCombinational_body);
}

void SV3_1aTreeShapeListener::exitSequential_body(
    SV3_1aParser::Sequential_bodyContext *ctx) {
  if (ctx->ENDTABLE())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDTABLE(),
               VObjectType::paENDTABLE);
  addVObject(ctx, VObjectType::paSequential_body);
}

void SV3_1aTreeShapeListener::exitClocking_declaration(
    SV3_1aParser::Clocking_declarationContext *ctx) {
  if (ctx->DEFAULT())
    addVObject((antlr4::ParserRuleContext *)ctx->DEFAULT(),
               VObjectType::paDEFAULT);
  if (ctx->GLOBAL())
    addVObject((antlr4::ParserRuleContext *)ctx->GLOBAL(),
               VObjectType::paGLOBAL);
  if (ctx->ENDCLOCKING())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDCLOCKING(),
               VObjectType::paENDCLOCKING);
  addVObject(ctx, VObjectType::paClocking_declaration);
}

void SV3_1aTreeShapeListener::exitPackage_declaration(
    SV3_1aParser::Package_declarationContext *ctx) {
  if (ctx->ENDPACKAGE())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDPACKAGE(),
               VObjectType::paENDPACKAGE);
  addVObject(ctx, VObjectType::paPackage_declaration);
}

void SV3_1aTreeShapeListener::enterProgram_declaration(
    SV3_1aParser::Program_declarationContext *ctx) {
  std::string ident;
  if (ctx->program_ansi_header()) {
    ident = ctx->program_ansi_header()->identifier()->getText();
    if (ctx->program_ansi_header()->PROGRAM()) {
      addVObject(
          (antlr4::ParserRuleContext *)ctx->program_ansi_header()->PROGRAM(),
          VObjectType::paPROGRAM);
    }
  } else if (ctx->program_nonansi_header()) {
    ident = ctx->program_nonansi_header()->identifier()->getText();
    if (ctx->program_nonansi_header()->PROGRAM()) {
      addVObject(
          (antlr4::ParserRuleContext *)ctx->program_nonansi_header()->PROGRAM(),
          VObjectType::paPROGRAM);
    }
  } else {
    if (ctx->identifier(0))
      ident = ctx->identifier(0)->getText();
    else
      ident = "PROGRAM NAME UNKNOWN";
    if (ctx->PROGRAM()) {
      addVObject((antlr4::ParserRuleContext *)ctx->PROGRAM(),
                 VObjectType::paPROGRAM);
    }
  }
  ident = std::regex_replace(ident, std::regex(EscapeSequence), "");
  addDesignElement(ctx, ident, DesignElement::Program, VObjectType::paPROGRAM);
}

void SV3_1aTreeShapeListener::enterClass_declaration(
    SV3_1aParser::Class_declarationContext *ctx) {
  std::string ident;
  if (ctx->identifier(0)) {
    ident = ctx->identifier(0)->getText();
    ident = std::regex_replace(ident, std::regex(EscapeSequence), "");
    addDesignElement(ctx, ident, DesignElement::Class, VObjectType::paCLASS);
  } else
    addDesignElement(ctx, "UNNAMED_CLASS", DesignElement::Class,
                     VObjectType::paCLASS);
}

SV3_1aTreeShapeListener::SV3_1aTreeShapeListener(
    ParseFile *pf, antlr4::CommonTokenStream *tokens, uint32_t lineOffset)
    : SV3_1aTreeShapeHelper::SV3_1aTreeShapeHelper(pf, tokens, lineOffset) {}

SV3_1aTreeShapeListener::~SV3_1aTreeShapeListener() {}

void SV3_1aTreeShapeListener::enterPackage_declaration(
    SV3_1aParser::Package_declarationContext *ctx) {
  if (ctx->PACKAGE()) {
    addVObject((antlr4::ParserRuleContext *)ctx->PACKAGE(),
               VObjectType::paPACKAGE);
  }
  std::string ident = ctx->identifier(0)->getText();
  ident = std::regex_replace(ident, std::regex(EscapeSequence), "");
  addDesignElement(ctx, ident, DesignElement::Package, VObjectType::paPACKAGE);
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
  ParseUtils::LineColumn lineCol =
      ParseUtils::getLineColumn(ctx->TICK_TIMESCALE());
  compUnitTimeInfo.m_line = lineCol.first;
  std::regex base_regex("`timescale([0-9]+)([mnsupf]+)/([0-9]+)([mnsupf]+)");
  std::smatch base_match;
  const std::string value = ctx->getText();
  if (std::regex_match(value, base_match, base_regex)) {
    std::ssub_match base1_sub_match = base_match[1];
    std::string base1 = base1_sub_match.str();
    compUnitTimeInfo.m_timeUnitValue = std::stoi(base1);
    if ((compUnitTimeInfo.m_timeUnitValue != 1) &&
        (compUnitTimeInfo.m_timeUnitValue != 10) &&
        (compUnitTimeInfo.m_timeUnitValue != 100)) {
      logError(ErrorDefinition::PA_TIMESCALE_INVALID_VALUE, ctx, base1);
    }
    compUnitTimeInfo.m_timeUnit = TimeInfo::unitFromString(base_match[2].str());
    std::ssub_match base2_sub_match = base_match[3];
    std::string base2 = base2_sub_match.str();
    compUnitTimeInfo.m_timePrecisionValue = std::stoi(base2);
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
  addVObject(ctx->time_unit(), s, VObjectType::paTime_unit);
  addVObject(ctx, VObjectType::paTime_literal);
}

void SV3_1aTreeShapeListener::exitTime_unit(
    SV3_1aParser::Time_unitContext *ctx) {
  const std::string &s = ctx->getText();
  if ((s == "s") || (s == "ms") || (s == "us") || (s == "ns") || (s == "ps") ||
      (s == "fs")) {
    addVObject(ctx, ctx->getText(), VObjectType::paTime_unit);
  } else {
    addVObject((antlr4::ParserRuleContext *)ctx->Simple_identifier(),
               ctx->getText(), VObjectType::slStringConst);
    addVObject(ctx, VObjectType::paName_of_instance);
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

void SV3_1aTreeShapeListener::enterUdp_declaration(
    SV3_1aParser::Udp_declarationContext *ctx) {
  std::string ident;
  if (ctx->udp_ansi_declaration()) {
    ident = ctx->udp_ansi_declaration()->identifier()->getText();
    if (ctx->udp_ansi_declaration()->PRIMITIVE()) {
      addVObject(
          (antlr4::ParserRuleContext *)ctx->udp_ansi_declaration()->PRIMITIVE(),
          VObjectType::paPRIMITIVE);
    }
  } else if (ctx->udp_nonansi_declaration()) {
    ident = ctx->udp_nonansi_declaration()->identifier()->getText();
    if (ctx->udp_nonansi_declaration()->PRIMITIVE()) {
      addVObject((antlr4::ParserRuleContext *)ctx->udp_nonansi_declaration()
                     ->PRIMITIVE(),
                 VObjectType::paPRIMITIVE);
    }
  } else {
    if (ctx->identifier(0)) {
      ident = ctx->identifier(0)->getText();
    } else {
      ident = "UDP NAME UNKNOWN";
    }
    if (ctx->PRIMITIVE()) {
      addVObject((antlr4::ParserRuleContext *)ctx->PRIMITIVE(),
                 VObjectType::paPRIMITIVE);
    }
  }
  ident = std::regex_replace(ident, std::regex(EscapeSequence), "");
  addDesignElement(ctx, ident, DesignElement::Primitive,
                   VObjectType::paPRIMITIVE);
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
  VObjectType type = VObjectType::paZ;
  if (s == "z" || s == "Z") {
    type = VObjectType::paZ;
  } else if (s == "x" || s == "X") {
    type = VObjectType::paX;
  }
  addVObject(ctx, s, type);
}

/*
void
SV3_1aTreeShapeListener::exitComment_OneLine
(SV3_1aParser::Comment_OneLineContext *ctx)
{
  addVObject (ctx, ctx->One_line_comment ()->getText (),
VObjectType::paComments);
}

void
SV3_1aTreeShapeListener::exitComment_Block (SV3_1aParser::Comment_BlockContext
*ctx)
{
  addVObject (ctx, ctx->Block_comment ()->getText (), VObjectType::paComments);
}
*/

void SV3_1aTreeShapeListener::exitPound_delay_value(
    SV3_1aParser::Pound_delay_valueContext *ctx) {
  if (ctx->Pound_delay()) {
    addVObject(ctx, ctx->Pound_delay()->getText(), VObjectType::slIntConst);
  } else if (ctx->Pound_Pound_delay()) {
    addVObject(ctx, ctx->Pound_Pound_delay()->getText(),
               VObjectType::paPound_Pound_delay);
  } else if (ctx->delay_value()) {
    const std::string text = ctx->delay_value()->getText();
    if (std::isdigit(text[0])) {
      addVObject(ctx, text, VObjectType::slIntConst);
    } else {
      addVObject(ctx, text, VObjectType::slStringConst);
    }
  }
}

void SV3_1aTreeShapeListener::exitData_type(
    SV3_1aParser::Data_typeContext *ctx) {
  if (ctx->VIRTUAL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->VIRTUAL(),
               VObjectType::paVIRTUAL);
  }
  addVObject(ctx, VObjectType::paData_type);
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
    ident = StringUtils::rtrim(ident);
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
               VObjectType::paPRIORITY);
  } else if (ctx->UNIQUE()) {
    addVObject((antlr4::ParserRuleContext *)ctx->UNIQUE(),
               VObjectType::paUNIQUE);
  } else if (ctx->UNIQUE0()) {
    addVObject((antlr4::ParserRuleContext *)ctx->UNIQUE0(),
               VObjectType::paUNIQUE0);
  }
  addVObject(ctx, VObjectType::paUnique_priority);
}

void SV3_1aTreeShapeListener::exitCase_keyword(
    SV3_1aParser::Case_keywordContext *ctx) {
  if (ctx->CASE()) {
    addVObject((antlr4::ParserRuleContext *)ctx->CASE(), VObjectType::paCASE);
  } else if (ctx->CASEX()) {
    addVObject((antlr4::ParserRuleContext *)ctx->CASEX(), VObjectType::paCASEX);
  } else if (ctx->CASEZ()) {
    addVObject((antlr4::ParserRuleContext *)ctx->CASEZ(), VObjectType::paCASEZ);
  }
  addVObject(ctx, VObjectType::paCase_keyword);
}

void SV3_1aTreeShapeListener::exitPart_select_op_colon(
    SV3_1aParser::Part_select_op_colonContext *ctx) {
  if (ctx->INC_PART_SELECT_OP()) {
    addVObject(ctx, VObjectType::paIncPartSelectOp);
  } else if (ctx->DEC_PART_SELECT_OP()) {
    addVObject(ctx, VObjectType::paDecPartSelectOp);
  } else if (ctx->COLON()) {
    addVObject(ctx, VObjectType::paColonPartSelectOp);
  }
}

void SV3_1aTreeShapeListener::exitPart_select_op(
    SV3_1aParser::Part_select_opContext *ctx) {
  if (ctx->INC_PART_SELECT_OP()) {
    addVObject(ctx, VObjectType::paIncPartSelectOp);
  } else if (ctx->DEC_PART_SELECT_OP()) {
    addVObject(ctx, VObjectType::paDecPartSelectOp);
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
  else if (!ctx->Simple_identifier().empty())
    addVObject((antlr4::ParserRuleContext *)ctx->Simple_identifier()[0], ident,
               VObjectType::slStringConst);
  else if (ctx->SIGNED())
    addVObject((antlr4::ParserRuleContext *)ctx->SIGNED(), ident,
               VObjectType::slStringConst);
  else if (ctx->UNSIGNED())
    addVObject((antlr4::ParserRuleContext *)ctx->UNSIGNED(), ident,
               VObjectType::slStringConst);
  addVObject(ctx, VObjectType::paSystem_task_names);
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
  addVObject(ctx, VObjectType::paClass_type);

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

  addVObject(ctx, VObjectType::paHierarchical_identifier);
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
               VObjectType::paENDPROGRAM);
  addVObject(ctx, VObjectType::paAnonymous_program);
}

void SV3_1aTreeShapeListener::exitProgram_declaration(
    SV3_1aParser::Program_declarationContext *ctx) {
  if (ctx->ENDPROGRAM())
    addVObject((antlr4::ParserRuleContext *)ctx->ENDPROGRAM(),
               VObjectType::paENDPROGRAM);
  addVObject(ctx, VObjectType::paProgram_declaration);
}

void SV3_1aTreeShapeListener::exitProcedural_continuous_assignment(
    SV3_1aParser::Procedural_continuous_assignmentContext *ctx) {
  if (ctx->ASSIGN()) {
    addVObject((antlr4::ParserRuleContext *)ctx->ASSIGN(),
               VObjectType::paASSIGN);
  } else if (ctx->DEASSIGN()) {
    addVObject((antlr4::ParserRuleContext *)ctx->DEASSIGN(),
               VObjectType::paDEASSIGN);
  } else if (ctx->FORCE()) {
    addVObject((antlr4::ParserRuleContext *)ctx->FORCE(), VObjectType::paFORCE);
  } else if (ctx->RELEASE()) {
    addVObject((antlr4::ParserRuleContext *)ctx->RELEASE(),
               VObjectType::paRELEASE);
  }
  addVObject(ctx, VObjectType::paProcedural_continuous_assignment);
}

void SV3_1aTreeShapeListener::exitDrive_strength(
    SV3_1aParser::Drive_strengthContext *ctx) {
  if (ctx->SUPPLY0()) {
    addVObject((antlr4::ParserRuleContext *)ctx->SUPPLY0(),
               VObjectType::paSUPPLY0);
  } else if (ctx->STRONG0()) {
    addVObject((antlr4::ParserRuleContext *)ctx->STRONG0(),
               VObjectType::paSTRONG0);
  } else if (ctx->PULL0()) {
    addVObject((antlr4::ParserRuleContext *)ctx->PULL0(), VObjectType::paPULL0);
  } else if (ctx->WEAK0()) {
    addVObject((antlr4::ParserRuleContext *)ctx->WEAK0(), VObjectType::paWEAK0);
  }
  if (ctx->SUPPLY1()) {
    addVObject((antlr4::ParserRuleContext *)ctx->SUPPLY1(),
               VObjectType::paSUPPLY1);
  } else if (ctx->STRONG1()) {
    addVObject((antlr4::ParserRuleContext *)ctx->STRONG1(),
               VObjectType::paSTRONG1);
  } else if (ctx->PULL1()) {
    addVObject((antlr4::ParserRuleContext *)ctx->PULL1(), VObjectType::paPULL1);
  } else if (ctx->WEAK1()) {
    addVObject((antlr4::ParserRuleContext *)ctx->WEAK1(), VObjectType::paWEAK1);
  }

  if (ctx->HIGHZ0()) {
    addVObject((antlr4::ParserRuleContext *)ctx->HIGHZ0(),
               VObjectType::paHIGHZ0);
  } else if (ctx->HIGHZ1()) {
    addVObject((antlr4::ParserRuleContext *)ctx->HIGHZ1(),
               VObjectType::paHIGHZ1);
  }
  addVObject(ctx, VObjectType::paDrive_strength);
}

void SV3_1aTreeShapeListener::exitStrength0(
    SV3_1aParser::Strength0Context *ctx) {
  if (ctx->SUPPLY0()) {
    addVObject((antlr4::ParserRuleContext *)ctx->SUPPLY0(),
               VObjectType::paSUPPLY0);
  } else if (ctx->STRONG0()) {
    addVObject((antlr4::ParserRuleContext *)ctx->STRONG0(),
               VObjectType::paSTRONG0);
  } else if (ctx->PULL0()) {
    addVObject((antlr4::ParserRuleContext *)ctx->PULL0(), VObjectType::paPULL0);
  } else if (ctx->WEAK0()) {
    addVObject((antlr4::ParserRuleContext *)ctx->WEAK0(), VObjectType::paWEAK0);
  }
  addVObject(ctx, VObjectType::paStrength0);
}

void SV3_1aTreeShapeListener::exitAction_block(
    SV3_1aParser::Action_blockContext *ctx) {
  if (ctx->ELSE()) {
    addVObject((antlr4::ParserRuleContext *)ctx->ELSE(), VObjectType::paELSE);
  }
  addVObject(ctx, VObjectType::paAction_block);
}

void SV3_1aTreeShapeListener::exitEvent_trigger(
    SV3_1aParser::Event_triggerContext *ctx) {
  if (ctx->IMPLY())
    addVObject((antlr4::ParserRuleContext *)ctx->IMPLY(),
               VObjectType::paBinOp_Imply);
  if (ctx->NON_BLOCKING_TRIGGER_EVENT_OP())
    addVObject(
        (antlr4::ParserRuleContext *)ctx->NON_BLOCKING_TRIGGER_EVENT_OP(),
        VObjectType::paNON_BLOCKING_TRIGGER_EVENT_OP);
  addVObject(ctx, VObjectType::paEvent_trigger);
}

void SV3_1aTreeShapeListener::exitStrength1(
    SV3_1aParser::Strength1Context *ctx) {
  if (ctx->SUPPLY1()) {
    addVObject((antlr4::ParserRuleContext *)ctx->SUPPLY1(),
               VObjectType::paSUPPLY1);
  } else if (ctx->STRONG1()) {
    addVObject((antlr4::ParserRuleContext *)ctx->STRONG1(),
               VObjectType::paSTRONG1);
  } else if (ctx->PULL1()) {
    addVObject((antlr4::ParserRuleContext *)ctx->PULL1(), VObjectType::paPULL1);
  } else if (ctx->WEAK1()) {
    addVObject((antlr4::ParserRuleContext *)ctx->WEAK1(), VObjectType::paWEAK1);
  }
  addVObject(ctx, VObjectType::paStrength1);
}

void SV3_1aTreeShapeListener::exitCharge_strength(
    SV3_1aParser::Charge_strengthContext *ctx) {
  if (ctx->SMALL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->SMALL(), VObjectType::paSMALL);
  } else if (ctx->MEDIUM()) {
    addVObject((antlr4::ParserRuleContext *)ctx->MEDIUM(),
               VObjectType::paMEDIUM);
  } else if (ctx->LARGE()) {
    addVObject((antlr4::ParserRuleContext *)ctx->LARGE(), VObjectType::paLARGE);
  }
  addVObject(ctx, VObjectType::paCharge_strength);
}

void SV3_1aTreeShapeListener::exitStream_operator(
    SV3_1aParser::Stream_operatorContext *ctx) {
  if (ctx->SHIFT_RIGHT()) {
    addVObject((antlr4::ParserRuleContext *)ctx->SHIFT_RIGHT(),
               VObjectType::paBinOp_ShiftRight);
  } else if (ctx->SHIFT_LEFT()) {
    addVObject((antlr4::ParserRuleContext *)ctx->SHIFT_LEFT(),
               VObjectType::paBinOp_ShiftLeft);
  }
  addVObject(ctx, VObjectType::paStream_operator);
}

void SV3_1aTreeShapeListener::exitLoop_statement(
    SV3_1aParser::Loop_statementContext *ctx) {
  if (ctx->DO()) {
    addVObject((antlr4::ParserRuleContext *)ctx->DO(), VObjectType::paDO);
  } else if (ctx->FOREVER()) {
    addVObject((antlr4::ParserRuleContext *)ctx->FOREVER(),
               VObjectType::paFOREVER);
  } else if (ctx->REPEAT()) {
    addVObject((antlr4::ParserRuleContext *)ctx->REPEAT(),
               VObjectType::paREPEAT);
  } else if (ctx->WHILE()) {
    addVObject((antlr4::ParserRuleContext *)ctx->WHILE(), VObjectType::paWHILE);
  } else if (ctx->FOR()) {
    addVObject((antlr4::ParserRuleContext *)ctx->FOR(), VObjectType::paFOR);
  } else if (ctx->FOREACH()) {
    addVObject((antlr4::ParserRuleContext *)ctx->FOREACH(),
               VObjectType::paFOREACH);
  }
  addVObject(ctx, VObjectType::paLoop_statement);
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
  addVObject(ctx, VObjectType::paPackage_scope);

  if (ident.size() > SV_MAX_IDENTIFIER_SIZE) {
    logError(ErrorDefinition::PA_MAX_LENGTH_IDENTIFIER, ctx, ident);
  }
}

void SV3_1aTreeShapeListener::exitPs_identifier(
    SV3_1aParser::Ps_identifierContext *ctx) {
  std::string ident;
  antlr4::ParserRuleContext *childCtx = nullptr;
  if (!ctx->Simple_identifier().empty()) {
    childCtx = (antlr4::ParserRuleContext *)ctx->Simple_identifier()[0];
    ident = ctx->Simple_identifier()[0]->getText();
    if (ctx->Simple_identifier().size() > 1) {
      ident += "::" + ctx->Simple_identifier()[1]->getText();
    }
  } else if (!ctx->Escaped_identifier().empty()) {
    childCtx = (antlr4::ParserRuleContext *)ctx->Escaped_identifier()[0];
    ident = ctx->Escaped_identifier()[0]->getText();
    std::regex escaped(std::string(EscapeSequence) + std::string("(.*?)") +
                       EscapeSequence);
    std::smatch match;
    while (std::regex_search(ident, match, escaped)) {
      std::string var = match[1].str();
      ident = ident.replace(match.position(0), match.length(0), var);
    }
  } else if (!ctx->THIS().empty()) {
    childCtx = (antlr4::ParserRuleContext *)ctx->THIS()[0];
    ident = ctx->THIS()[0]->getText();
  } else if (!ctx->RANDOMIZE().empty()) {
    childCtx = (antlr4::ParserRuleContext *)ctx->RANDOMIZE()[0];
    ident = ctx->RANDOMIZE()[0]->getText();
  } else if (!ctx->SAMPLE().empty()) {
    childCtx = (antlr4::ParserRuleContext *)ctx->SAMPLE()[0];
    ident = ctx->SAMPLE()[0]->getText();
  } else if (ctx->DOLLAR_UNIT()) {
    childCtx = (antlr4::ParserRuleContext *)ctx->DOLLAR_UNIT();
    ident = ctx->DOLLAR_UNIT()->getText();
  }
  addVObject(childCtx, ident, VObjectType::slStringConst);
  addVObject(ctx, VObjectType::paPs_identifier);

  if (ident.size() > SV_MAX_IDENTIFIER_SIZE) {
    logError(ErrorDefinition::PA_MAX_LENGTH_IDENTIFIER, ctx, ident);
  }
}

void SV3_1aTreeShapeListener::exitExpression(
    SV3_1aParser::ExpressionContext *ctx) {
  if (ctx->MATCHES()) {
    addVObject((antlr4::ParserRuleContext *)ctx->MATCHES(),
               VObjectType::paMatches);
  }
  if (ctx->PLUS()) {
    if (ctx->expression().size() == 1)
      addVObject((antlr4::ParserRuleContext *)ctx->PLUS(),
                 VObjectType::paUnary_Plus);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->PLUS(),
                 VObjectType::paBinOp_Plus);
  } else if (ctx->MINUS()) {
    if (ctx->expression().size() == 1)
      addVObject((antlr4::ParserRuleContext *)ctx->MINUS(),
                 VObjectType::paUnary_Minus);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->MINUS(),
                 VObjectType::paBinOp_Minus);
  } else if (ctx->BANG()) {
    addVObject((antlr4::ParserRuleContext *)ctx->BANG(),
               VObjectType::paUnary_Not);
  } else if (ctx->TILDA()) {
    addVObject((antlr4::ParserRuleContext *)ctx->TILDA(),
               VObjectType::paUnary_Tilda);
  } else if (ctx->BITW_AND()) {
    if (ctx->expression().size() == 1)
      addVObject((antlr4::ParserRuleContext *)ctx->BITW_AND(),
                 VObjectType::paUnary_BitwAnd);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->BITW_AND(),
                 VObjectType::paBinOp_BitwAnd);
  } else if (ctx->BITW_OR()) {
    if (ctx->expression().size() == 1)
      addVObject((antlr4::ParserRuleContext *)ctx->BITW_OR(),
                 VObjectType::paUnary_BitwOr);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->BITW_OR(),
                 VObjectType::paBinOp_BitwOr);
  } else if (ctx->BITW_XOR()) {
    if (ctx->expression().size() == 1)
      addVObject((antlr4::ParserRuleContext *)ctx->BITW_XOR(),
                 VObjectType::paUnary_BitwXor);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->BITW_XOR(),
                 VObjectType::paBinOp_BitwXor);
  } else if (ctx->REDUCTION_NAND()) {
    if (ctx->expression().size() == 1)
      addVObject((antlr4::ParserRuleContext *)ctx->REDUCTION_NAND(),
                 VObjectType::paUnary_ReductNand);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->REDUCTION_NAND(),
                 VObjectType::paBinOp_ReductNand);
  } else if (ctx->REDUCTION_NOR()) {
    addVObject((antlr4::ParserRuleContext *)ctx->REDUCTION_NOR(),
               VObjectType::paUnary_ReductNor);
  } else if (ctx->REDUCTION_XNOR1()) {
    if (ctx->expression().size() == 1)
      addVObject((antlr4::ParserRuleContext *)ctx->REDUCTION_XNOR1(),
                 VObjectType::paUnary_ReductXnor1);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->REDUCTION_XNOR1(),
                 VObjectType::paBinOp_ReductXnor1);
  } else if (ctx->REDUCTION_XNOR2()) {
    if (ctx->expression().size() == 1)
      addVObject((antlr4::ParserRuleContext *)ctx->REDUCTION_XNOR2(),
                 VObjectType::paUnary_ReductXnor2);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->REDUCTION_XNOR2(),
                 VObjectType::paBinOp_ReductXnor2);
  } else if (ctx->STARSTAR()) {
    addVObject((antlr4::ParserRuleContext *)ctx->STARSTAR(),
               VObjectType::paBinOp_MultMult);
  } else if (ctx->STAR()) {
    addVObject((antlr4::ParserRuleContext *)ctx->STAR(),
               VObjectType::paBinOp_Mult);
  } else if (ctx->DIV()) {
    addVObject((antlr4::ParserRuleContext *)ctx->DIV(),
               VObjectType::paBinOp_Div);
  } else if (ctx->PERCENT()) {
    addVObject((antlr4::ParserRuleContext *)ctx->PERCENT(),
               VObjectType::paBinOp_Percent);
  } else if (ctx->SHIFT_RIGHT()) {
    addVObject((antlr4::ParserRuleContext *)ctx->SHIFT_RIGHT(),
               VObjectType::paBinOp_ShiftRight);
  } else if (ctx->SHIFT_LEFT()) {
    addVObject((antlr4::ParserRuleContext *)ctx->SHIFT_LEFT(),
               VObjectType::paBinOp_ShiftLeft);
  } else if (ctx->ARITH_SHIFT_RIGHT()) {
    addVObject((antlr4::ParserRuleContext *)ctx->ARITH_SHIFT_RIGHT(),
               VObjectType::paBinOp_ArithShiftRight);
  } else if (ctx->ARITH_SHIFT_LEFT()) {
    addVObject((antlr4::ParserRuleContext *)ctx->ARITH_SHIFT_LEFT(),
               VObjectType::paBinOp_ArithShiftLeft);
  } else if (ctx->LESS()) {
    addVObject((antlr4::ParserRuleContext *)ctx->LESS(),
               VObjectType::paBinOp_Less);
  } else if (ctx->LESS_EQUAL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->LESS_EQUAL(),
               VObjectType::paBinOp_LessEqual);
  } else if (ctx->PLUSPLUS()) {
    addVObject((antlr4::ParserRuleContext *)ctx->PLUSPLUS(),
               VObjectType::paIncDec_PlusPlus);
  } else if (ctx->MINUSMINUS()) {
    addVObject((antlr4::ParserRuleContext *)ctx->MINUSMINUS(),
               VObjectType::paIncDec_MinusMinus);
  } else if (ctx->GREATER()) {
    addVObject((antlr4::ParserRuleContext *)ctx->GREATER(),
               VObjectType::paBinOp_Great);
  } else if (ctx->GREATER_EQUAL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->GREATER_EQUAL(),
               VObjectType::paBinOp_GreatEqual);
  } else if (ctx->INSIDE()) {
    addVObject((antlr4::ParserRuleContext *)ctx->INSIDE(),
               VObjectType::paINSIDE);
  } else if (ctx->EQUIV()) {
    addVObject((antlr4::ParserRuleContext *)ctx->EQUIV(),
               VObjectType::paBinOp_Equiv);
  } else if (ctx->NOTEQUAL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->NOTEQUAL(),
               VObjectType::paBinOp_Not);
  } else if (ctx->BINARY_WILDCARD_EQUAL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->BINARY_WILDCARD_EQUAL(),
               VObjectType::paBinOp_WildcardEqual);
  } else if (ctx->BINARY_WILDCARD_NOTEQUAL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->BINARY_WILDCARD_NOTEQUAL(),
               VObjectType::paBinOp_WildcardNotEqual);
  } else if (ctx->FOUR_STATE_LOGIC_EQUAL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->FOUR_STATE_LOGIC_EQUAL(),
               VObjectType::paBinOp_FourStateLogicEqual);
  } else if (ctx->FOUR_STATE_LOGIC_NOTEQUAL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->FOUR_STATE_LOGIC_NOTEQUAL(),
               VObjectType::paBinOp_FourStateLogicNotEqual);
  } else if (ctx->WILD_EQUAL_OP()) {
    addVObject((antlr4::ParserRuleContext *)ctx->WILD_EQUAL_OP(),
               VObjectType::paBinOp_WildEqual);
  } else if (ctx->WILD_NOTEQUAL_OP()) {
    addVObject((antlr4::ParserRuleContext *)ctx->WILD_NOTEQUAL_OP(),
               VObjectType::paBinOp_WildEqual);
  } else if (ctx->BITW_AND()) {
    if (ctx->expression().size() == 1)
      addVObject((antlr4::ParserRuleContext *)ctx->BITW_AND(),
                 VObjectType::paUnary_BitwAnd);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->BITW_AND(),
                 VObjectType::paBinOp_BitwAnd);
  } else if (!ctx->LOGICAL_AND().empty()) {
    addVObject((antlr4::ParserRuleContext *)ctx->LOGICAL_AND()[0],
               VObjectType::paBinOp_LogicAnd);
  } else if (ctx->LOGICAL_OR()) {
    addVObject((antlr4::ParserRuleContext *)ctx->LOGICAL_OR(),
               VObjectType::paBinOp_LogicOr);
  } else if (ctx->IMPLY()) {
    addVObject((antlr4::ParserRuleContext *)ctx->IMPLY(),
               VObjectType::paBinOp_Imply);
  } else if (ctx->EQUIVALENCE()) {
    addVObject((antlr4::ParserRuleContext *)ctx->EQUIVALENCE(),
               VObjectType::paBinOp_Equivalence);
  } else if (ctx->TAGGED()) {
    addVObject((antlr4::ParserRuleContext *)ctx->TAGGED(),
               VObjectType::paTAGGED);
  }
  if (ctx->QMARK()) {
    addVObject((antlr4::ParserRuleContext *)ctx->QMARK(), VObjectType::paQMARK);
  }
  addVObject(ctx, VObjectType::paExpression);
}

void SV3_1aTreeShapeListener::exitEvent_expression(
    SV3_1aParser::Event_expressionContext *ctx) {
  if (ctx->IFF()) {
    addVObject((antlr4::ParserRuleContext *)ctx->IFF(), VObjectType::paIFF);
  }
  addVObject(ctx, VObjectType::paEvent_expression);
}

void SV3_1aTreeShapeListener::exitConstant_expression(
    SV3_1aParser::Constant_expressionContext *ctx) {
  if (ctx->PLUS()) {
    if (ctx->constant_primary())
      addVObject((antlr4::ParserRuleContext *)ctx->PLUS(),
                 VObjectType::paUnary_Plus);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->PLUS(),
                 VObjectType::paBinOp_Plus);
  } else if (ctx->MINUS()) {
    if (ctx->constant_primary())
      addVObject((antlr4::ParserRuleContext *)ctx->MINUS(),
                 VObjectType::paUnary_Minus);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->MINUS(),
                 VObjectType::paBinOp_Minus);
  } else if (ctx->BANG()) {
    addVObject((antlr4::ParserRuleContext *)ctx->BANG(),
               VObjectType::paUnary_Not);
  } else if (ctx->TILDA()) {
    addVObject((antlr4::ParserRuleContext *)ctx->TILDA(),
               VObjectType::paUnary_Tilda);
  } else if (ctx->BITW_AND()) {
    if (ctx->constant_primary())
      addVObject((antlr4::ParserRuleContext *)ctx->BITW_AND(),
                 VObjectType::paUnary_BitwAnd);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->BITW_AND(),
                 VObjectType::paBinOp_BitwAnd);
  } else if (ctx->BITW_OR()) {
    if (ctx->constant_primary())
      addVObject((antlr4::ParserRuleContext *)ctx->BITW_OR(),
                 VObjectType::paUnary_BitwOr);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->BITW_OR(),
                 VObjectType::paBinOp_BitwOr);
  } else if (ctx->BITW_XOR()) {
    if (ctx->constant_primary())
      addVObject((antlr4::ParserRuleContext *)ctx->BITW_XOR(),
                 VObjectType::paUnary_BitwXor);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->BITW_XOR(),
                 VObjectType::paBinOp_BitwXor);
  } else if (ctx->REDUCTION_NAND()) {
    if (ctx->constant_primary())
      addVObject((antlr4::ParserRuleContext *)ctx->REDUCTION_NAND(),
                 VObjectType::paUnary_ReductNand);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->REDUCTION_NAND(),
                 VObjectType::paBinOp_ReductNand);
  } else if (ctx->REDUCTION_NOR()) {
    addVObject((antlr4::ParserRuleContext *)ctx->REDUCTION_NOR(),
               VObjectType::paUnary_ReductNor);
  } else if (ctx->REDUCTION_XNOR1()) {
    if (ctx->constant_primary())
      addVObject((antlr4::ParserRuleContext *)ctx->REDUCTION_XNOR1(),
                 VObjectType::paUnary_ReductXnor1);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->REDUCTION_XNOR1(),
                 VObjectType::paBinOp_ReductXnor1);
  } else if (ctx->REDUCTION_XNOR2()) {
    if (ctx->constant_primary())
      addVObject((antlr4::ParserRuleContext *)ctx->REDUCTION_XNOR2(),
                 VObjectType::paUnary_ReductXnor2);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->REDUCTION_XNOR2(),
                 VObjectType::paBinOp_ReductXnor2);
  } else if (ctx->STARSTAR()) {
    addVObject((antlr4::ParserRuleContext *)ctx->STARSTAR(),
               VObjectType::paBinOp_MultMult);
  } else if (ctx->STAR()) {
    addVObject((antlr4::ParserRuleContext *)ctx->STAR(),
               VObjectType::paBinOp_Mult);
  } else if (ctx->DIV()) {
    addVObject((antlr4::ParserRuleContext *)ctx->DIV(),
               VObjectType::paBinOp_Div);
  } else if (ctx->PERCENT()) {
    addVObject((antlr4::ParserRuleContext *)ctx->PERCENT(),
               VObjectType::paBinOp_Percent);
  } else if (ctx->SHIFT_RIGHT()) {
    addVObject((antlr4::ParserRuleContext *)ctx->SHIFT_RIGHT(),
               VObjectType::paBinOp_ShiftRight);
  } else if (ctx->SHIFT_LEFT()) {
    addVObject((antlr4::ParserRuleContext *)ctx->SHIFT_LEFT(),
               VObjectType::paBinOp_ShiftLeft);
  } else if (ctx->ARITH_SHIFT_RIGHT()) {
    addVObject((antlr4::ParserRuleContext *)ctx->ARITH_SHIFT_RIGHT(),
               VObjectType::paBinOp_ArithShiftRight);
  } else if (ctx->ARITH_SHIFT_LEFT()) {
    addVObject((antlr4::ParserRuleContext *)ctx->ARITH_SHIFT_LEFT(),
               VObjectType::paBinOp_ArithShiftLeft);
  } else if (ctx->LESS()) {
    addVObject((antlr4::ParserRuleContext *)ctx->LESS(),
               VObjectType::paBinOp_Less);
  } else if (ctx->LESS_EQUAL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->LESS_EQUAL(),
               VObjectType::paBinOp_LessEqual);
  } else if (ctx->GREATER()) {
    addVObject((antlr4::ParserRuleContext *)ctx->GREATER(),
               VObjectType::paBinOp_Great);
  } else if (ctx->GREATER_EQUAL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->GREATER_EQUAL(),
               VObjectType::paBinOp_GreatEqual);
  } else if (ctx->INSIDE()) {
    addVObject((antlr4::ParserRuleContext *)ctx->INSIDE(),
               VObjectType::paINSIDE);
  } else if (ctx->EQUIV()) {
    addVObject((antlr4::ParserRuleContext *)ctx->EQUIV(),
               VObjectType::paBinOp_Equiv);
  } else if (ctx->NOTEQUAL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->NOTEQUAL(),
               VObjectType::paBinOp_Not);
  } else if (ctx->BINARY_WILDCARD_EQUAL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->BINARY_WILDCARD_EQUAL(),
               VObjectType::paBinOp_WildcardEqual);
  } else if (ctx->BINARY_WILDCARD_NOTEQUAL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->BINARY_WILDCARD_NOTEQUAL(),
               VObjectType::paBinOp_WildcardNotEqual);
  } else if (ctx->FOUR_STATE_LOGIC_EQUAL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->FOUR_STATE_LOGIC_EQUAL(),
               VObjectType::paBinOp_FourStateLogicEqual);
  } else if (ctx->FOUR_STATE_LOGIC_NOTEQUAL()) {
    addVObject((antlr4::ParserRuleContext *)ctx->FOUR_STATE_LOGIC_NOTEQUAL(),
               VObjectType::paBinOp_FourStateLogicNotEqual);
  } else if (ctx->WILD_EQUAL_OP()) {
    addVObject((antlr4::ParserRuleContext *)ctx->WILD_EQUAL_OP(),
               VObjectType::paBinOp_WildEqual);
  } else if (ctx->WILD_NOTEQUAL_OP()) {
    addVObject((antlr4::ParserRuleContext *)ctx->WILD_NOTEQUAL_OP(),
               VObjectType::paBinOp_WildEqual);
  } else if (ctx->BITW_AND()) {
    if (ctx->constant_primary())
      addVObject((antlr4::ParserRuleContext *)ctx->BITW_AND(),
                 VObjectType::paUnary_BitwAnd);
    else
      addVObject((antlr4::ParserRuleContext *)ctx->BITW_AND(),
                 VObjectType::paBinOp_BitwAnd);
  } else if (!ctx->LOGICAL_AND().empty()) {
    addVObject((antlr4::ParserRuleContext *)ctx->LOGICAL_AND()[0],
               VObjectType::paBinOp_LogicAnd);
  } else if (ctx->LOGICAL_OR()) {
    addVObject((antlr4::ParserRuleContext *)ctx->LOGICAL_OR(),
               VObjectType::paBinOp_LogicOr);
  } else if (ctx->IMPLY()) {
    addVObject((antlr4::ParserRuleContext *)ctx->IMPLY(),
               VObjectType::paBinOp_Imply);
  } else if (ctx->EQUIVALENCE()) {
    addVObject((antlr4::ParserRuleContext *)ctx->EQUIVALENCE(),
               VObjectType::paBinOp_Equivalence);
  }
  addVObject(ctx, VObjectType::paConstant_expression);
}

void SV3_1aTreeShapeListener::exitNet_type(SV3_1aParser::Net_typeContext *ctx) {
  if (ctx->SUPPLY0()) {
    addVObject(ctx, VObjectType::paNetType_Supply0);
  } else if (ctx->SUPPLY1()) {
    addVObject(ctx, VObjectType::paNetType_Supply1);
  } else if (ctx->TRI()) {
    addVObject(ctx, VObjectType::paNetType_Tri);
  } else if (ctx->TRIAND()) {
    addVObject(ctx, VObjectType::paNetType_TriAnd);
  } else if (ctx->TRIOR()) {
    addVObject(ctx, VObjectType::paNetType_TriOr);
  } else if (ctx->TRIREG()) {
    addVObject(ctx, VObjectType::paNetType_TriReg);
  } else if (ctx->TRI0()) {
    addVObject(ctx, VObjectType::paNetType_Tri0);
  } else if (ctx->TRI1()) {
    addVObject(ctx, VObjectType::paNetType_Tri1);
  } else if (ctx->UWIRE()) {
    addVObject(ctx, VObjectType::paNetType_Uwire);
  } else if (ctx->WIRE()) {
    addVObject(ctx, VObjectType::paNetType_Wire);
  } else if (ctx->WAND()) {
    addVObject(ctx, VObjectType::paNetType_Wand);
  } else if (ctx->WOR()) {
    addVObject(ctx, VObjectType::paNetType_Wor);
  }
}

void SV3_1aTreeShapeListener::exitAssignment_operator(
    SV3_1aParser::Assignment_operatorContext *ctx) {
  if (ctx->ASSIGN_OP()) {
    addVObject(ctx, VObjectType::paAssignOp_Assign);
  } else if (ctx->ADD_ASSIGN()) {
    addVObject(ctx, VObjectType::paAssignOp_Add);
  } else if (ctx->SUB_ASSIGN()) {
    addVObject(ctx, VObjectType::paAssignOp_Sub);
  } else if (ctx->MULT_ASSIGN()) {
    addVObject(ctx, VObjectType::paAssignOp_Mult);
  } else if (ctx->DIV_ASSIGN()) {
    addVObject(ctx, VObjectType::paAssignOp_Div);
  } else if (ctx->MODULO_ASSIGN()) {
    addVObject(ctx, VObjectType::paAssignOp_Modulo);
  } else if (ctx->BITW_AND_ASSIGN()) {
    addVObject(ctx, VObjectType::paAssignOp_BitwAnd);
  } else if (ctx->BITW_OR_ASSIGN()) {
    addVObject(ctx, VObjectType::paAssignOp_BitwOr);
  } else if (ctx->BITW_XOR_ASSIGN()) {
    addVObject(ctx, VObjectType::paAssignOp_BitwXor);
  } else if (ctx->BITW_LEFT_SHIFT_ASSIGN()) {
    addVObject(ctx, VObjectType::paAssignOp_BitwLeftShift);
  } else if (ctx->BITW_RIGHT_SHIFT_ASSIGN()) {
    addVObject(ctx, VObjectType::paAssignOp_BitwRightShift);
  } else if (ctx->ARITH_SHIFT_LEFT_ASSIGN()) {
    addVObject(ctx, VObjectType::paAssignOp_ArithShiftLeft);
  } else if (ctx->ARITH_SHIFT_RIGHT_ASSIGN()) {
    addVObject(ctx, VObjectType::paAssignOp_ArithShiftRight);
  }
}

void SV3_1aTreeShapeListener::exitInc_or_dec_operator(
    SV3_1aParser::Inc_or_dec_operatorContext *ctx) {
  if (ctx->PLUSPLUS())
    addVObject(ctx, VObjectType::paIncDec_PlusPlus);
  else
    addVObject(ctx, VObjectType::paIncDec_MinusMinus);
}

void SV3_1aTreeShapeListener::exitGate_instantiation(
    SV3_1aParser::Gate_instantiationContext *ctx) {
  if (ctx->PULLUP()) {
    addVObject((antlr4::ParserRuleContext *)ctx->PULLUP(),
               VObjectType::paPULLUP);
  } else if (ctx->PULLDOWN()) {
    addVObject((antlr4::ParserRuleContext *)ctx->PULLDOWN(),
               VObjectType::paPULLDOWN);
  }
  addVObject(ctx, VObjectType::paGate_instantiation);
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
  addVObject(ctx, VObjectType::paOutput_symbol);
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
               VObjectType::paPound_Pound_delay);
  }
  addVObject(ctx, VObjectType::paCycle_delay);
}

void SV3_1aTreeShapeListener::exitCycle_delay_range(
    SV3_1aParser::Cycle_delay_rangeContext *ctx) {
  if (ctx->Pound_Pound_delay()) {
    addVObject((antlr4::ParserRuleContext *)ctx->Pound_Pound_delay(),
               ctx->Pound_Pound_delay()->getText(),
               VObjectType::paPound_Pound_delay);
  }
  if (ctx->POUNDPOUND()) {
    addVObject((antlr4::ParserRuleContext *)ctx->POUNDPOUND(),
               ctx->POUNDPOUND()->getText(), VObjectType::paPound_Pound_delay);
  }
  if (ctx->PLUS()) {
    addVObject((antlr4::ParserRuleContext *)ctx->PLUS(),
               VObjectType::paUnary_Plus);
  }
  if (ctx->ASSOCIATIVE_UNSPECIFIED()) {
    addVObject((antlr4::ParserRuleContext *)ctx->ASSOCIATIVE_UNSPECIFIED(),
               VObjectType::paAssociative_dimension);
  }
  addVObject(ctx, VObjectType::paCycle_delay_range);
}

void SV3_1aTreeShapeListener::exitSequence_expr(
    SV3_1aParser::Sequence_exprContext *ctx) {
  if (ctx->WITHIN()) {
    addVObject((antlr4::ParserRuleContext *)ctx->WITHIN(),
               VObjectType::paWITHIN);
  }
  if (ctx->THROUGHOUT()) {
    addVObject((antlr4::ParserRuleContext *)ctx->THROUGHOUT(),
               VObjectType::paTHROUGHOUT);
  }
  if (ctx->FIRST_MATCH()) {
    addVObject((antlr4::ParserRuleContext *)ctx->FIRST_MATCH(),
               VObjectType::paFIRST_MATCH);
  }
  if (ctx->INTERSECT()) {
    addVObject((antlr4::ParserRuleContext *)ctx->INTERSECT(),
               VObjectType::paINTERSECT);
  }
  if (ctx->AND()) {
    addVObject((antlr4::ParserRuleContext *)ctx->AND(), VObjectType::paAND);
  }
  if (ctx->OR()) {
    addVObject((antlr4::ParserRuleContext *)ctx->OR(), VObjectType::paOR);
  }
  addVObject(ctx, VObjectType::paSequence_expr);
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
    addVObject((antlr4::ParserRuleContext *)ctx->QMARK(), VObjectType::paQMARK);
  }
  addVObject(ctx, VObjectType::paLevel_symbol);
}

void SV3_1aTreeShapeListener::exitEdge_symbol(
    SV3_1aParser::Edge_symbolContext *ctx) {
  if (ctx->Simple_identifier()) {
    std::string ident = ctx->Simple_identifier()->getText();
    addVObject((antlr4::ParserRuleContext *)ctx->Simple_identifier(), ident,
               VObjectType::slStringConst);
  } else if (ctx->STAR()) {
    addVObject((antlr4::ParserRuleContext *)ctx->STAR(),
               VObjectType::paBinOp_Mult);
  }
  addVObject(ctx, VObjectType::paEdge_symbol);
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
    addVObject((antlr4::ParserRuleContext *)ctx->WITH(), VObjectType::paWITH);
  }
  addVObject(ctx, VObjectType::paRandomize_call);
}

void SV3_1aTreeShapeListener::exitDeferred_immediate_assert_statement(
    SV3_1aParser::Deferred_immediate_assert_statementContext *ctx) {
  if (ctx->Pound_delay()) {
    addVObject((antlr4::ParserRuleContext *)ctx->Pound_delay(),
               ctx->Pound_delay()->getText(), VObjectType::paPound_delay);
  } else if (ctx->Pound_Pound_delay()) {
    addVObject((antlr4::ParserRuleContext *)ctx->Pound_Pound_delay(),
               ctx->Pound_Pound_delay()->getText(),
               VObjectType::paPound_Pound_delay);
  }
  addVObject(ctx, VObjectType::paDeferred_immediate_assert_statement);
}

void SV3_1aTreeShapeListener::exitDeferred_immediate_assume_statement(
    SV3_1aParser::Deferred_immediate_assume_statementContext *ctx) {
  if (ctx->Pound_delay()) {
    addVObject((antlr4::ParserRuleContext *)ctx->Pound_delay(),
               ctx->Pound_delay()->getText(), VObjectType::paPound_delay);
  } else if (ctx->Pound_Pound_delay()) {
    addVObject((antlr4::ParserRuleContext *)ctx->Pound_Pound_delay(),
               ctx->Pound_Pound_delay()->getText(),
               VObjectType::paPound_Pound_delay);
  }
  addVObject(ctx, VObjectType::paDeferred_immediate_assume_statement);
}

void SV3_1aTreeShapeListener::exitDeferred_immediate_cover_statement(
    SV3_1aParser::Deferred_immediate_cover_statementContext *ctx) {
  if (ctx->Pound_delay()) {
    addVObject((antlr4::ParserRuleContext *)ctx->Pound_delay(),
               ctx->Pound_delay()->getText(), VObjectType::paPound_delay);
  } else if (ctx->Pound_Pound_delay()) {
    addVObject((antlr4::ParserRuleContext *)ctx->Pound_Pound_delay(),
               ctx->Pound_Pound_delay()->getText(),
               VObjectType::paPound_Pound_delay);
  }
  addVObject(ctx, VObjectType::paDeferred_immediate_cover_statement);
}

void SV3_1aTreeShapeListener::exitLocal_parameter_declaration(
    SV3_1aParser::Local_parameter_declarationContext *ctx) {
  if (ctx->TYPE()) {
    addVObject((antlr4::ParserRuleContext *)ctx->TYPE(), VObjectType::paTYPE);
  }
  addVObject(ctx, VObjectType::paLocal_parameter_declaration);
}

void SV3_1aTreeShapeListener::exitParameter_declaration(
    SV3_1aParser::Parameter_declarationContext *ctx) {
  if (ctx->TYPE()) {
    addVObject((antlr4::ParserRuleContext *)ctx->TYPE(), VObjectType::paTYPE);
  }
  addVObject(ctx, VObjectType::paParameter_declaration);
}

void SV3_1aTreeShapeListener::exitPort_direction(
    SV3_1aParser::Port_directionContext *ctx) {
  if (ctx->INPUT()) {
    addVObject(ctx, VObjectType::paPortDir_Inp);
  } else if (ctx->OUTPUT()) {
    addVObject(ctx, VObjectType::paPortDir_Out);
  } else if (ctx->INOUT()) {
    addVObject(ctx, VObjectType::paPortDir_Inout);
  } else if (ctx->REF()) {
    addVObject(ctx, VObjectType::paPortDir_Ref);
  }
}

void SV3_1aTreeShapeListener::exitInteger_atom_type(
    SV3_1aParser::Integer_atom_typeContext *ctx) {
  if (ctx->INT())
    addVObject(ctx, VObjectType::paIntegerAtomType_Int);
  else if (ctx->BYTE())
    addVObject(ctx, VObjectType::paIntegerAtomType_Byte);
  else if (ctx->SHORTINT())
    addVObject(ctx, VObjectType::paIntegerAtomType_Shortint);
  else if (ctx->LONGINT())
    addVObject(ctx, VObjectType::paIntegerAtomType_LongInt);
  else if (ctx->INTEGER())
    addVObject(ctx, VObjectType::paIntegerAtomType_Integer);
  else if (ctx->TIME())
    addVObject(ctx, VObjectType::paIntegerAtomType_Time);
}

void SV3_1aTreeShapeListener::exitInteger_vector_type(
    SV3_1aParser::Integer_vector_typeContext *ctx) {
  if (ctx->LOGIC())
    addVObject(ctx, VObjectType::paIntVec_TypeLogic);
  else if (ctx->REG())
    addVObject(ctx, VObjectType::paIntVec_TypeReg);
  else if (ctx->BIT())
    addVObject(ctx, VObjectType::paIntVec_TypeBit);
}

void SV3_1aTreeShapeListener::exitNon_integer_type(
    SV3_1aParser::Non_integer_typeContext *ctx) {
  if (ctx->SHORTREAL())
    addVObject(ctx, VObjectType::paNonIntType_ShortReal);
  else if (ctx->REAL())
    addVObject(ctx, VObjectType::paNonIntType_Real);
  else if (ctx->REALTIME())
    addVObject(ctx, VObjectType::paNonIntType_RealTime);
}

void SV3_1aTreeShapeListener::exitAlways_keyword(
    SV3_1aParser::Always_keywordContext *ctx) {
  if (ctx->ALWAYS_COMB()) {
    addVObject(ctx, VObjectType::paALWAYS_COMB);
  } else if (ctx->ALWAYS_FF()) {
    addVObject(ctx, VObjectType::paALWAYS_FF);
  } else if (ctx->ALWAYS_LATCH()) {
    addVObject(ctx, VObjectType::paALWAYS_LATCH);
  } else if (ctx->ALWAYS()) {
    addVObject(ctx, VObjectType::paALWAYS);
  }
}

void SV3_1aTreeShapeListener::exitEdge_identifier(
    SV3_1aParser::Edge_identifierContext *ctx) {
  if (ctx->POSEDGE())
    addVObject(ctx, VObjectType::paEdge_Posedge);
  else if (ctx->NEGEDGE())
    addVObject(ctx, VObjectType::paEdge_Negedge);
  else if (ctx->EDGE())
    addVObject(ctx, VObjectType::paEdge_Edge);
}

void SV3_1aTreeShapeListener::exitNumber(SV3_1aParser::NumberContext *ctx) {
  if (ctx->Integral_number()) {
    auto number = ctx->Integral_number();
    addVObject(ctx, number->getText(), VObjectType::slIntConst);
  } else if (ctx->Real_number())
    addVObject(ctx, ctx->Real_number()->getText(), VObjectType::slRealConst);
  else if (ctx->ONE_TICK_b0())
    addVObject(ctx, VObjectType::paNumber_1Tickb0);
  else if (ctx->ONE_TICK_b1())
    addVObject(ctx, VObjectType::paNumber_1Tickb1);
  else if (ctx->ONE_TICK_B0())
    addVObject(ctx, VObjectType::paNumber_1TickB0);
  else if (ctx->ONE_TICK_B1())
    addVObject(ctx, VObjectType::paNumber_1TickB1);
  else if (ctx->TICK_b0())
    addVObject(ctx, VObjectType::paNumber_Tickb0);
  else if (ctx->TICK_b1())
    addVObject(ctx, VObjectType::paNumber_Tickb1);
  else if (ctx->TICK_B0())
    addVObject(ctx, VObjectType::paNumber_TickB0);
  else if (ctx->TICK_B1())
    addVObject(ctx, VObjectType::paNumber_TickB1);
  else if (ctx->TICK_0())
    addVObject(ctx, VObjectType::paNumber_Tick0);
  else if (ctx->TICK_1())
    addVObject(ctx, VObjectType::paNumber_Tick1);
  else if (ctx->ONE_TICK_bx())
    addVObject(ctx, VObjectType::paNumber_1Tickbx);
  else if (ctx->ONE_TICK_bX())
    addVObject(ctx, VObjectType::paNumber_1TickbX);
  else if (ctx->ONE_TICK_Bx())
    addVObject(ctx, VObjectType::paNumber_1TickBx);
  else if (ctx->ONE_TICK_BX())
    addVObject(ctx, VObjectType::paNumber_1TickbX);
}

void SV3_1aTreeShapeListener::exitSigning(SV3_1aParser::SigningContext *ctx) {
  if (ctx->SIGNED())
    addVObject(ctx, VObjectType::paSigning_Signed);
  else if (ctx->UNSIGNED())
    addVObject(ctx, VObjectType::paSigning_Unsigned);
}

void SV3_1aTreeShapeListener::exitTf_port_direction(
    SV3_1aParser::Tf_port_directionContext *ctx) {
  if (ctx->INPUT())
    addVObject(ctx, VObjectType::paTfPortDir_Inp);
  else if (ctx->OUTPUT())
    addVObject(ctx, VObjectType::paTfPortDir_Out);
  else if (ctx->INOUT())
    addVObject(ctx, VObjectType::paTfPortDir_Inout);
  else if (ctx->REF())
    addVObject(ctx, VObjectType::paTfPortDir_Ref);
  else if (ctx->CONST())
    addVObject(ctx, VObjectType::paTfPortDir_ConstRef);
}

void SV3_1aTreeShapeListener::exitDefault_nettype_directive(
    SV3_1aParser::Default_nettype_directiveContext *ctx) {
  NetTypeInfo info;
  info.m_type = VObjectType::paNetType_Wire;
  info.m_fileId = m_pf->getFileId(0);
  ParseUtils::LineColumn lineCol = ParseUtils::getLineColumn(m_tokens, ctx);
  info.m_line = lineCol.first;
  if (ctx->Simple_identifier()) {
    addVObject((antlr4::ParserRuleContext *)ctx->Simple_identifier(),
               ctx->Simple_identifier()->getText(), VObjectType::slStringConst);
    info.m_type = VObjectType::slNoType;
  } else if (ctx->net_type()) {
    if (ctx->net_type()->SUPPLY0())
      info.m_type = VObjectType::paSUPPLY0;
    else if (ctx->net_type()->SUPPLY1())
      info.m_type = VObjectType::paSUPPLY1;
    else if (ctx->net_type()->WIRE())
      info.m_type = VObjectType::paNetType_Wire;
    else if (ctx->net_type()->UWIRE())
      info.m_type = VObjectType::paNetType_Uwire;
    else if (ctx->net_type()->WAND())
      info.m_type = VObjectType::paNetType_Wand;
    else if (ctx->net_type()->WOR())
      info.m_type = VObjectType::paNetType_Wor;
    else if (ctx->net_type()->TRI())
      info.m_type = VObjectType::paNetType_Tri;
    else if (ctx->net_type()->TRIREG())
      info.m_type = VObjectType::paNetType_TriReg;
    else if (ctx->net_type()->TRIOR())
      info.m_type = VObjectType::paNetType_TriOr;
    else if (ctx->net_type()->TRIAND())
      info.m_type = VObjectType::paNetType_TriAnd;
    else if (ctx->net_type()->TRI0())
      info.m_type = VObjectType::paNetType_Tri0;
    else if (ctx->net_type()->TRI1())
      info.m_type = VObjectType::paNetType_Tri1;
  }
  addVObject(ctx, VObjectType::paDefault_nettype_directive);
  m_pf->getCompilationUnit()->recordDefaultNetType(info);
}

void SV3_1aTreeShapeListener::exitParameter_value_assignment(
    SV3_1aParser::Parameter_value_assignmentContext *ctx) {
  if (ctx->Pound_delay()) {
    addVObject(ctx, ctx->Pound_delay()->getText(), VObjectType::slIntConst);
  }
  addVObject(ctx, VObjectType::paParameter_value_assignment);
}

void SV3_1aTreeShapeListener::exitElaboration_system_task(
    SV3_1aParser::Elaboration_system_taskContext *ctx) {
  if (ctx->number()) {
    addVObject((antlr4::ParserRuleContext *)ctx->number(),
               ctx->number()->getText(), VObjectType::slIntConst);
  }
  addVObject((antlr4::ParserRuleContext *)ctx->Simple_identifier(),
             ctx->Simple_identifier()->getText(), VObjectType::slStringConst);
  addVObject(ctx, VObjectType::paElaboration_system_task);
}

}  // namespace SURELOG
