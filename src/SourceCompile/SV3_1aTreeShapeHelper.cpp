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
 * File:   SV3_1aTreeShapeHelper.cpp
 * Author: alain
 *
 * Created on June 25, 2017, 2:51 PM
 */

#include "Surelog/SourceCompile/SV3_1aTreeShapeHelper.h"

#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/NodeId.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/ErrorReporting/ErrorContainer.h"
#include "Surelog/Library/Library.h"
#include "Surelog/SourceCompile/CompilationUnit.h"
#include "Surelog/SourceCompile/CompileSourceFile.h"
#include "Surelog/SourceCompile/ParseFile.h"
#include "Surelog/SourceCompile/SymbolTable.h"
#include "Surelog/SourceCompile/VObjectTypes.h"
#include "Surelog/Utils/ParseUtils.h"
#include "Surelog/Utils/StringUtils.h"

namespace SURELOG {

SV3_1aTreeShapeHelper::SV3_1aTreeShapeHelper(ParseFile* pf,
                                             antlr4::CommonTokenStream* tokens,

                                             uint32_t lineOffset)
    : CommonListenerHelper(nullptr, tokens),
      m_pf(pf),
      m_currentElement(nullptr),
      m_lineOffset(lineOffset) {
  if (pf->getCompileSourceFile()) {
    m_ppOutputFileLocation = pf->getCompileSourceFile()
                                 ->getCommandLineParser()
                                 ->usePPOutputFileLocation();
  } else {
    m_ppOutputFileLocation = false;
  }
}

SV3_1aTreeShapeHelper::SV3_1aTreeShapeHelper(ParseLibraryDef* pf,
                                             antlr4::CommonTokenStream* tokens)
    : CommonListenerHelper(nullptr, tokens),
      m_pf(nullptr),
      m_currentElement(nullptr),
      m_lineOffset(0),
      m_ppOutputFileLocation(false) {}

void SV3_1aTreeShapeHelper::logError(ErrorDefinition::ErrorType error,
                                     antlr4::ParserRuleContext* ctx,
                                     std::string_view object,
                                     bool printColumn) {
  ParseUtils::LineColumn lineCol = ParseUtils::getLineColumn(m_tokens, ctx);

  Location loc(
      m_pf->getFileId(lineCol.first /*+ m_lineOffset*/),
      m_pf->getLineNb(lineCol.first /*+ m_lineOffset*/),
      printColumn ? lineCol.second : 0,
      m_pf->getCompileSourceFile()->getSymbolTable()->registerSymbol(object));
  Error err(error, loc);
  m_pf->addError(err);
}

void SV3_1aTreeShapeHelper::logError(ErrorDefinition::ErrorType error,
                                     Location& loc, bool showDuplicates) {
  Error err(error, loc);
  m_pf->getCompileSourceFile()->getErrorContainer()->addError(err,
                                                              showDuplicates);
}

void SV3_1aTreeShapeHelper::logError(ErrorDefinition::ErrorType error,
                                     Location& loc, Location& extraLoc,
                                     bool showDuplicates) {
  std::vector<Location> extras;
  extras.push_back(extraLoc);
  Error err(error, loc, &extras);
  m_pf->getCompileSourceFile()->getErrorContainer()->addError(err,
                                                              showDuplicates);
}

NodeId SV3_1aTreeShapeHelper::generateDesignElemId() {
  return m_pf->getCompilationUnit()->generateUniqueDesignElemId();
}

NodeId SV3_1aTreeShapeHelper::generateNodeId() {
  return m_pf->getCompilationUnit()->generateUniqueNodeId();
}

SymbolId SV3_1aTreeShapeHelper::registerSymbol(std::string_view symbol) {
  return m_pf->getSymbolTable()->registerSymbol(symbol);
}

void SV3_1aTreeShapeHelper::addNestedDesignElement(
    antlr4::ParserRuleContext* ctx, std::string_view name,
    DesignElement::ElemType elemtype, VObjectType objtype) {
  auto [fileId, line, column, endLine, endColumn] = getFileLine(ctx, nullptr);
  const std::string design_element =
      StrCat(m_pf->getLibrary()->getName(), "@", name);
  DesignElement* elem = new DesignElement(
      registerSymbol(name), fileId, elemtype, generateDesignElemId(), line,
      column, endLine, endColumn, InvalidNodeId);
  elem->m_context = ctx;
  elem->m_timeInfo = m_pf->getCompilationUnit()->getTimeInfo(fileId, line);
  elem->m_defaultNetType =
      m_pf->getCompilationUnit()->getDefaultNetType(fileId, line);
  if (!m_nestedElements.empty()) {
    elem->m_timeInfo = m_nestedElements.top()->m_timeInfo;
    elem->m_parent = m_nestedElements.top()->m_uniqueId;
  }
  m_fileContent->addDesignElement(design_element, elem);
  m_currentElement = m_fileContent->getDesignElements().back();
  m_nestedElements.push(m_currentElement);
}

void SV3_1aTreeShapeHelper::addDesignElement(antlr4::ParserRuleContext* ctx,
                                             std::string_view name,
                                             DesignElement::ElemType elemtype,
                                             VObjectType objtype) {
  auto [fileId, line, column, endLine, endColumn] = getFileLine(ctx, nullptr);
  const std::string design_element =
      StrCat(m_pf->getLibrary()->getName(), "@", name);
  DesignElement* elem = new DesignElement(
      registerSymbol(name), fileId, elemtype, generateDesignElemId(), line,
      column, endLine, endColumn, InvalidNodeId);
  elem->m_context = ctx;
  elem->m_timeInfo =
      m_pf->getCompilationUnit()->getTimeInfo(m_pf->getFileId(line), line);
  elem->m_defaultNetType =
      m_pf->getCompilationUnit()->getDefaultNetType(fileId, line);
  m_fileContent->addDesignElement(design_element, elem);
  m_currentElement = m_fileContent->getDesignElements().back();
}

std::tuple<PathId, uint32_t, uint16_t, uint32_t, uint16_t>
SV3_1aTreeShapeHelper::getFileLine(antlr4::ParserRuleContext* ctx,
                                   antlr4::Token* token) const {
  ParseUtils::LineColumn lineCol =
      (token == nullptr) ? ParseUtils::getLineColumn(m_tokens, ctx)
                         : ParseUtils::getLineColumn(token);
  ParseUtils::LineColumn endLineCol =
      (token == nullptr) ? ParseUtils::getEndLineColumn(m_tokens, ctx)
                         : ParseUtils::getEndLineColumn(token);
  uint32_t line = 0;
  uint16_t column = 0;
  uint32_t endLine = 0;
  uint16_t endColumn = 0;
  PathId fileId;
  if (m_ppOutputFileLocation || !m_pf->getPpFileId()) {
    fileId = m_pf->getFileId(0);
    line = lineCol.first;
    column = lineCol.second;
    endLine = endLineCol.first;
    endColumn = endLineCol.second;
  } else {
    fileId = m_pf->getFileId(lineCol.first + m_lineOffset);
    line = m_pf->getLineNb(lineCol.first + m_lineOffset);
    column = lineCol.second;
    endLine = m_pf->getLineNb(endLineCol.first + m_lineOffset);
    endColumn = endLineCol.second;
  }
  return std::make_tuple(fileId, line, column, endLine, endColumn);
}

std::pair<double, TimeInfo::Unit> SV3_1aTreeShapeHelper::getTimeValue(
    SV3_1aParser::Time_literalContext* ctx) {
  double actual_value = 0;
  TimeInfo::Unit unit = TimeInfo::Unit::Second;
  if (ctx->Integral_number())
    actual_value = atoi(ctx->Integral_number()->getText().c_str());
  if (ctx->Real_number())
    actual_value = atoi(ctx->Real_number()->getText().c_str());
  unit = TimeInfo::unitFromString(ctx->time_unit()->getText());

  return std::make_pair(actual_value, unit);
}
}  // namespace SURELOG
