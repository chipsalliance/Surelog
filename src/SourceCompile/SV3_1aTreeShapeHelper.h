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
 * File:   SV3_1aTreeShapeHelper.h
 * Author: alain
 *
 * Created on June 25, 2017, 2:51 PM
 */

#ifndef SV3_1ATREESHAPEHELPER_H
#define SV3_1ATREESHAPEHELPER_H
#include <stack>
#include <map>
#include <unordered_map>
#include "../Utils/ParseUtils.h"
#include "../SourceCompile/SymbolTable.h"
#include "../Design/TimeInfo.h"
#include "../Design/DesignElement.h"
#include "../Design/FileContent.h"
#include "ParseFile.h"
#include "CompilationUnit.h"
#include "CompileSourceFile.h"
#include "VObjectTypes.h"
#include "../Library/ParseLibraryDef.h"
#include "IncludeFileInfo.h"

namespace SURELOG {

#define SV_MAX_IDENTIFIER_SIZE 1024
#define SV_MAX_STRING_SIZE 4 * 1024 * 1024

class SV3_1aTreeShapeHelper {
 public:
  typedef enum {
    Verilog1995,
    Verilog2001,
    Verilog2005,
    Verilog2009,
    SystemVerilog
  } VerilogVersion;

  SV3_1aTreeShapeHelper(ParseFile* pf, antlr4::CommonTokenStream* tokens,
                        unsigned int lineOffset);
  SV3_1aTreeShapeHelper(ParseLibraryDef* pf, antlr4::CommonTokenStream* tokens);

  virtual ~SV3_1aTreeShapeHelper();

  void logError(ErrorDefinition::ErrorType error, ParserRuleContext* ctx,
                std::string object, bool printColumn = false);

  void logError(ErrorDefinition::ErrorType, Location& loc,
                bool showDuplicates = false);

  void logError(ErrorDefinition::ErrorType, Location& loc, Location& extraLoc,
                bool showDuplicates = false);

  NodeId generateDesignElemId();

  NodeId generateNodeId();

  SymbolId registerSymbol(std::string symbol);

  int registerObject(VObject& object);

  int LastObjIndex();

  int ObjectIndexFromContext(tree::ParseTree* ctx);

  VObject& Object(NodeId index);

  NodeId UniqueId(NodeId index);

  SymbolId& Name(NodeId index);

  NodeId& Child(NodeId index);

  NodeId& Sibling(NodeId index);

  NodeId& Definition(NodeId index);

  NodeId& Parent(NodeId index);

  unsigned short& Type(NodeId index);

  unsigned int& Line(NodeId index);

  void addNestedDesignElement(ParserRuleContext* ctx, std::string name,
                              DesignElement::ElemType elemtype,
                              VObjectType objtype);

  void addDesignElement(ParserRuleContext* ctx, std::string name,
                        DesignElement::ElemType elemtype, VObjectType objtype);

  int addVObject(ParserRuleContext* ctx, std::string name, VObjectType objtype);

  int addVObject(ParserRuleContext* ctx, VObjectType objtype);

  void addParentChildRelations(int indexParent, ParserRuleContext* ctx);

  NodeId getObjectId(ParserRuleContext* ctx);

  std::pair<double, TimeInfo::Unit> getTimeValue(
      SV3_1aParser::Time_literalContext* ctx);

  FileContent* getFileContent() { return m_fileContent; }

  unsigned int getFileLine(ParserRuleContext* ctx, SymbolId& fileId);

  void setVerilogVersion(VerilogVersion version) { m_version = version; }

  VerilogVersion getVerilogVersion() { return m_version; }

 protected:
  ParseFile* m_pf;
  FileContent* m_fileContent;
  DesignElement* m_currentElement;
  std::stack<DesignElement*> m_nestedElements;
  typedef std::unordered_map<tree::ParseTree*, NodeId> ContextToObjectMap;
  ContextToObjectMap m_contextToObjectMap;
  antlr4::CommonTokenStream* m_tokens;
  unsigned int m_lineOffset;
  bool m_ppOutputFileLocation;
  std::stack<IncludeFileInfo> m_includeFileInfo;
  VerilogVersion m_version;
};

};  // namespace SURELOG

#endif /* SV3_1ATREESHAPEHELPER_H */
