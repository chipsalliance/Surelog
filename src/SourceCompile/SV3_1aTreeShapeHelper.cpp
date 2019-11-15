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

#include "SymbolTable.h"
#include "../CommandLine/CommandLineParser.hpp"
#include "../ErrorReporting/ErrorContainer.h"
#include "CompilationUnit.h"
#include "PreprocessFile.h"
#include "CompileSourceFile.h"
#include "Compiler.h"
#include "ParseFile.h"

#include <cstdlib>
#include <iostream>
#include "antlr4-runtime.h"
using namespace std;
using namespace antlr4;
using namespace SURELOG;

#include "../parser/SV3_1aLexer.h"
#include "../parser/SV3_1aParser.h"
#include "../parser/SV3_1aParserBaseListener.h"
#include "SV3_1aTreeShapeHelper.h"
using namespace antlr4;
#include "../Utils/ParseUtils.h"
#include "SV3_1aTreeShapeHelper.h"

SV3_1aTreeShapeHelper::SV3_1aTreeShapeHelper(ParseFile* pf,
                                             antlr4::CommonTokenStream* tokens,
                                             unsigned int lineOffset)
    : m_pf(pf),
      m_fileContent(NULL),
      m_currentElement(NULL),
      m_tokens(tokens),
      m_lineOffset(lineOffset),
      m_version(SystemVerilog) {
  if (pf->getCompileSourceFile())
    m_ppOutputFileLocation = pf->getCompileSourceFile()
                                 ->getCommandLineParser()
                                 ->usePPOutoutFileLocation();
}

SV3_1aTreeShapeHelper::SV3_1aTreeShapeHelper(ParseLibraryDef* pf,
                                             antlr4::CommonTokenStream* tokens)
    : m_pf(NULL),
      m_fileContent(NULL),
      m_currentElement(NULL),
      m_tokens(tokens),
      m_lineOffset(0),
      m_ppOutputFileLocation(false),
      m_version(SystemVerilog) {}

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

SymbolId SV3_1aTreeShapeHelper::registerSymbol(std::string symbol) {
  return m_pf->getSymbolTable()->registerSymbol(symbol);
}

int SV3_1aTreeShapeHelper::registerObject(VObject& object) {
  m_fileContent->getVObjects().push_back(object);
  return LastObjIndex();
}

int SV3_1aTreeShapeHelper::LastObjIndex() {
  return m_fileContent->getVObjects().size() - 1;
}

int SV3_1aTreeShapeHelper::ObjectIndexFromContext(tree::ParseTree* ctx) {
  ContextToObjectMap::iterator itr = m_contextToObjectMap.find(ctx);
  if (itr == m_contextToObjectMap.end()) {
    return -1;
  } else {
    return (*itr).second;
  }
}

VObject& SV3_1aTreeShapeHelper::Object(NodeId index) {
  return m_fileContent->getVObjects()[index];
}

NodeId SV3_1aTreeShapeHelper::UniqueId(NodeId index) {
  // return m_fileContent->m_objects[index].m_uniqueId;
  return index;
}

SymbolId& SV3_1aTreeShapeHelper::Name(NodeId index) {
  return m_fileContent->getVObjects()[index].m_name;
}

NodeId& SV3_1aTreeShapeHelper::Child(NodeId index) {
  return m_fileContent->getVObjects()[index].m_child;
}

NodeId& SV3_1aTreeShapeHelper::Sibling(NodeId index) {
  return m_fileContent->getVObjects()[index].m_sibling;
}

NodeId& SV3_1aTreeShapeHelper::Definition(NodeId index) {
  return m_fileContent->getVObjects()[index].m_definition;
}

NodeId& SV3_1aTreeShapeHelper::Parent(NodeId index) {
  return m_fileContent->getVObjects()[index].m_parent;
}

unsigned short& SV3_1aTreeShapeHelper::Type(NodeId index) {
  return m_fileContent->getVObjects()[index].m_type;
}

unsigned int& SV3_1aTreeShapeHelper::Line(NodeId index) {
  return m_fileContent->getVObjects()[index].m_line;
}

void SV3_1aTreeShapeHelper::addNestedDesignElement(
    ParserRuleContext* ctx, std::string name, DesignElement::ElemType elemtype,
    VObjectType objtype) {
  SymbolId fileId;
  unsigned int line = getFileLine(ctx, fileId);

  DesignElement elem(registerSymbol(name), fileId, elemtype,
                     generateDesignElemId(), line, 0);
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
  unsigned int line = getFileLine(ctx, fileId);
  DesignElement elem(registerSymbol(name), fileId, elemtype,
                     generateDesignElemId(), line, 0);
  elem.m_context = ctx;
  elem.m_timeInfo =
      m_pf->getCompilationUnit()->getTimeInfo(m_pf->getFileId(line), line);
  m_fileContent->getDesignElements().push_back(elem);
  m_currentElement = &m_fileContent->getDesignElements().back();
}

unsigned int SV3_1aTreeShapeHelper::getFileLine(ParserRuleContext* ctx,
                                                SymbolId& fileId) {
  std::pair<int, int> lineCol = ParseUtils::getLineColumn(m_tokens, ctx);
  unsigned int line = 0;
  if (m_ppOutputFileLocation) {
    fileId = m_pf->getFileId(0);
    line = lineCol.first;
  } else {
    fileId = m_pf->getFileId(lineCol.first + m_lineOffset);
    line = m_pf->getLineNb(lineCol.first + m_lineOffset);
  }
  return line;
}

int SV3_1aTreeShapeHelper::addVObject(ParserRuleContext* ctx, std::string name,
                                      VObjectType objtype) {
  SymbolId fileId;
  unsigned int line = getFileLine(ctx, fileId);

  VObject object(registerSymbol(name), fileId, objtype, line, 0);
  m_fileContent->getVObjects().push_back(object);
  int objectIndex = m_fileContent->getVObjects().size() - 1;
  m_contextToObjectMap.insert(std::make_pair(ctx, objectIndex));
  addParentChildRelations(objectIndex, ctx);
  if (m_fileContent->getDesignElements().size()) {
    for (unsigned int i = 0; i <= m_fileContent->getDesignElements().size() - 1;
         i++) {
      DesignElement& elem =
          m_fileContent
              ->getDesignElements()[m_fileContent->getDesignElements().size() -
                                    1 - i];
      if (elem.m_context == ctx) {
        // Use the file and line number of the design object (package, module),
        // true file/line when splitting
        m_fileContent->getVObjects().back().m_fileId = elem.m_fileId;
        m_fileContent->getVObjects().back().m_line = elem.m_line;
        elem.m_node = objectIndex;
        break;
      }
    }
  }
  return objectIndex;
}

int SV3_1aTreeShapeHelper::addVObject(ParserRuleContext* ctx,
                                      VObjectType objtype) {
  SymbolId fileId;
  unsigned int line = getFileLine(ctx, fileId);

  VObject object(0, fileId, objtype, line, 0);
  m_fileContent->getVObjects().push_back(object);
  int objectIndex = m_fileContent->getVObjects().size() - 1;
  m_contextToObjectMap.insert(std::make_pair(ctx, objectIndex));
  addParentChildRelations(objectIndex, ctx);
  if (m_fileContent->getDesignElements().size()) {
    for (unsigned int i = 0; i <= m_fileContent->getDesignElements().size() - 1;
         i++) {
      DesignElement& elem =
          m_fileContent
              ->getDesignElements()[m_fileContent->getDesignElements().size() -
                                    1 - i];
      if (elem.m_context == ctx) {
        // Use the file and line number of the design object (package, module),
        // true file/line when splitting
        m_fileContent->getVObjects().back().m_fileId = elem.m_fileId;
        m_fileContent->getVObjects().back().m_line = elem.m_line;
        elem.m_node = objectIndex;
        break;
      }
    }
  }
  return objectIndex;
}

void SV3_1aTreeShapeHelper::addParentChildRelations(int indexParent,
                                                    ParserRuleContext* ctx) {
  int currentIndex = indexParent;
  for (tree::ParseTree* child : ctx->children) {
    int childIndex = ObjectIndexFromContext(child);
    if (childIndex != -1) {
      Parent(childIndex) = UniqueId(indexParent);
      if (currentIndex == indexParent) {
        Child(indexParent) = UniqueId(childIndex);
      } else {
        Sibling(currentIndex) = UniqueId(childIndex);
      }
      currentIndex = childIndex;
    }
  }
}

NodeId SV3_1aTreeShapeHelper::getObjectId(ParserRuleContext* ctx) {
  ContextToObjectMap::iterator itr = m_contextToObjectMap.find(ctx);
  if (itr == m_contextToObjectMap.end()) {
    return 0;
  } else {
    return (*itr).second;
  }
}

std::pair<double, TimeInfo::Unit> SV3_1aTreeShapeHelper::getTimeValue(
    SV3_1aParser::Time_literalContext* ctx) {
  double actual_value = 0;
  TimeInfo::Unit unit = TimeInfo::Second;
  if (ctx->Integral_number())
    actual_value = atoi(ctx->Integral_number()->getText().c_str());
  if (ctx->Real_number())
    actual_value = atoi(ctx->Real_number()->getText().c_str());
  unit = TimeInfo::unitFromString(ctx->time_unit()->getText());

  return std::make_pair(actual_value, unit);
}
