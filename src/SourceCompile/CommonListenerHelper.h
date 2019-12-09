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
 * File:   CommonListenerHelper.h
 * Author: alain
 *
 * Created on December 5, 2019, 9:13 PM
 */

#ifndef COMMONLISTENERHELPER_H
#define COMMONLISTENERHELPER_H

#include <stack>
#include <map>
#include <unordered_map>
#include "Utils/ParseUtils.h"
#include "SourceCompile/SymbolTable.h"
#include "Design/FileContent.h"
#include "SourceCompile/VObjectTypes.h"

namespace SURELOG {

static std::string EscapeSequence = "#~@";

class CommonListenerHelper {
public:
  CommonListenerHelper() : m_fileContent(NULL), m_tokens(NULL){}

  virtual ~CommonListenerHelper();
    
  virtual SymbolId registerSymbol(std::string symbol) = 0;

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

  int addVObject(ParserRuleContext* ctx, std::string name, VObjectType objtype);

  int addVObject(ParserRuleContext* ctx, VObjectType objtype);

  void addParentChildRelations(int indexParent, ParserRuleContext* ctx);

  NodeId getObjectId(ParserRuleContext* ctx);

  FileContent* getFileContent() { return m_fileContent; }

  virtual unsigned int getFileLine(ParserRuleContext* ctx, SymbolId& fileId) = 0;
     
protected:  
  FileContent* m_fileContent;
  typedef std::unordered_map<tree::ParseTree*, NodeId> ContextToObjectMap;
  ContextToObjectMap m_contextToObjectMap;
  antlr4::CommonTokenStream* m_tokens;

};

};


#endif /* COMMONLISTENERHELPER_H */

