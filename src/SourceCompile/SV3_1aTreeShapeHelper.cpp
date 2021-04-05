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

#include "SourceCompile/SymbolTable.h"
#include "CommandLine/CommandLineParser.h"
#include "ErrorReporting/ErrorContainer.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/Compiler.h"
#include "SourceCompile/ParseFile.h"

#include <cstdlib>
#include <iostream>
#include "antlr4-runtime.h"
using namespace std;
using namespace antlr4;
using namespace SURELOG;

#include "parser/SV3_1aLexer.h"
#include "parser/SV3_1aParser.h"
#include "parser/SV3_1aParserBaseListener.h"
#include "SourceCompile/SV3_1aTreeShapeHelper.h"
using namespace antlr4;
#include "Utils/ParseUtils.h"
#include "SourceCompile/SV3_1aTreeShapeHelper.h"

SV3_1aTreeShapeHelper::SV3_1aTreeShapeHelper(ParseFile* pf,
                                             antlr4::CommonTokenStream* tokens,
                                             unsigned int lineOffset)
    : CommonListenerHelper(), m_pf(pf),
      m_currentElement(NULL),
      m_lineOffset(lineOffset) {
  if (pf->getCompileSourceFile())
    m_ppOutputFileLocation = pf->getCompileSourceFile()
                                 ->getCommandLineParser()
                                 ->usePPOutputFileLocation();
  m_tokens = tokens;
}

SV3_1aTreeShapeHelper::SV3_1aTreeShapeHelper(ParseLibraryDef* pf,
                                             antlr4::CommonTokenStream* tokens)
    : CommonListenerHelper(), m_pf(NULL),
      m_currentElement(NULL),
      m_lineOffset(0),
      m_ppOutputFileLocation(false) {
  m_tokens = tokens;
}

SV3_1aTreeShapeHelper::~SV3_1aTreeShapeHelper() {}

void SV3_1aTreeShapeHelper::logError(ErrorDefinition::ErrorType error,
                                     ParserRuleContext* ctx, std::string object,
                                     bool printColumn) {
  std::pair<int, int> lineCol = ParseUtils::getLineColumn(m_tokens, ctx);

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

SymbolId SV3_1aTreeShapeHelper::registerSymbol(const std::string &symbol) {
  return m_pf->getSymbolTable()->registerSymbol(symbol);
}

void SV3_1aTreeShapeHelper::addNestedDesignElement(
    ParserRuleContext* ctx, std::string name, DesignElement::ElemType elemtype,
    VObjectType objtype) {
  SymbolId fileId;
  auto [line, column, endLine, endColumn] = getFileLine(ctx, fileId);

  DesignElement elem(registerSymbol(name), fileId, elemtype,
                     generateDesignElemId(), line, column, endLine, endColumn, 0);
  elem.m_context = ctx;
  elem.m_timeInfo =
      m_pf->getCompilationUnit()->getTimeInfo(m_pf->getFileId(line), line);
  if (m_nestedElements.size()) {
    elem.m_timeInfo = m_nestedElements.top()->m_timeInfo;
    elem.m_parent = m_nestedElements.top()->m_uniqueId;
  }
  m_fileContent->getDesignElements().push_back(elem);
  m_currentElement = &m_fileContent->getDesignElements().back();
  m_nestedElements.push(m_currentElement);
}

void SV3_1aTreeShapeHelper::addDesignElement(ParserRuleContext* ctx,
                                             std::string name,
                                             DesignElement::ElemType elemtype,
                                             VObjectType objtype) {
  SymbolId fileId;
  auto [line, column, endLine, endColumn] = getFileLine(ctx, fileId);
  DesignElement elem(registerSymbol(name), fileId, elemtype,
                     generateDesignElemId(), line, column, endLine, endColumn, 0);
  elem.m_context = ctx;
  elem.m_timeInfo =
      m_pf->getCompilationUnit()->getTimeInfo(m_pf->getFileId(line), line);
  m_fileContent->getDesignElements().push_back(elem);
  m_currentElement = &m_fileContent->getDesignElements().back();
}

std::tuple<unsigned int, unsigned short, unsigned int, unsigned short> SV3_1aTreeShapeHelper::getFileLine(ParserRuleContext* ctx,
                                                SymbolId& fileId) {
  std::pair<int, int> lineCol = ParseUtils::getLineColumn(m_tokens, ctx);
  std::pair<int, int> endLineCol = ParseUtils::getEndLineColumn(m_tokens, ctx);
  unsigned int line = 0;
  unsigned short column = 0;
  unsigned int endLine = 0;
  unsigned short endColumn = 0;
  if (m_ppOutputFileLocation) {
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
  return std::make_tuple(line, column, endLine, endColumn);
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
