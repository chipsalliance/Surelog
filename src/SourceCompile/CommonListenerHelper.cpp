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

#include "SourceCompile/CommonListenerHelper.h"

/*
 * File:   CommonListenerHelper.cpp
 * Author: alain
 *
 * Created on December 5, 2019, 9:13 PM
 */

#include <cstdlib>
#include <iostream>

#include "Utils/ParseUtils.h"
#include "antlr4-runtime.h"

using namespace std;
using namespace antlr4;
using namespace SURELOG;

CommonListenerHelper::~CommonListenerHelper()
{
}

int CommonListenerHelper::registerObject(VObject& object) {
  m_fileContent->getVObjects().push_back(object);
  return LastObjIndex();
}

int CommonListenerHelper::LastObjIndex() {
  return m_fileContent->getVObjects().size() - 1;
}

int CommonListenerHelper::ObjectIndexFromContext(
  const antlr4::tree::ParseTree* ctx) const {
  auto found = m_contextToObjectMap.find(ctx);
  return (found == m_contextToObjectMap.end()) ? -1 : found->second;
}

VObject& CommonListenerHelper::Object(NodeId index) {
  return m_fileContent->getVObjects()[index];
}

NodeId CommonListenerHelper::UniqueId(NodeId index) {
  return index;
}

SymbolId& CommonListenerHelper::Name(NodeId index) {
  return m_fileContent->getVObjects()[index].m_name;
}

NodeId& CommonListenerHelper::Child(NodeId index) {
  return m_fileContent->getVObjects()[index].m_child;
}

NodeId& CommonListenerHelper::Sibling(NodeId index) {
  return m_fileContent->getVObjects()[index].m_sibling;
}

NodeId& CommonListenerHelper::Definition(NodeId index) {
  return m_fileContent->getVObjects()[index].m_definition;
}

NodeId& CommonListenerHelper::Parent(NodeId index) {
  return m_fileContent->getVObjects()[index].m_parent;
}

unsigned short& CommonListenerHelper::Type(NodeId index) {
  return m_fileContent->getVObjects()[index].m_type;
}

unsigned short& CommonListenerHelper::Column(NodeId index) {
  return m_fileContent->getVObjects()[index].m_column;
}

unsigned int& CommonListenerHelper::Line(NodeId index) {
  return m_fileContent->getVObjects()[index].m_line;
}

int CommonListenerHelper::addVObject(ParserRuleContext* ctx, SymbolId sym, VObjectType objtype) {
  SymbolId fileId;
  auto [line, column, endLine, endColumn] = getFileLine(ctx, fileId);

  m_fileContent->getVObjects().emplace_back(sym, fileId, objtype, line, column, endLine, endColumn, 0);
  int objectIndex = m_fileContent->getVObjects().size() - 1;
  m_contextToObjectMap.insert(std::make_pair(ctx, objectIndex));
  addParentChildRelations(objectIndex, ctx);
  auto &delements = m_fileContent->getDesignElements();
  for (auto it = delements.rbegin(); it != delements.rend(); ++it) {
    if (it->m_context == ctx) {
      // Use the file and line number of the design object (package, module),
      // true file/line when splitting
      m_fileContent->getVObjects().back().m_fileId = it->m_fileId;
      m_fileContent->getVObjects().back().m_line = it->m_line;
      it->m_node = objectIndex;
      break;
    }
  }
  return objectIndex;
}

int CommonListenerHelper::addVObject(ParserRuleContext* ctx,
                                     const std::string &name,
                                     VObjectType objtype) {
  return addVObject(ctx, registerSymbol(name), objtype);
}

int CommonListenerHelper::addVObject(ParserRuleContext* ctx,
                                     VObjectType objtype) {
  return addVObject(ctx, 0, objtype);
}

void CommonListenerHelper::addParentChildRelations(int indexParent,
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

NodeId CommonListenerHelper::getObjectId(ParserRuleContext* ctx) {
  ContextToObjectMap::iterator itr = m_contextToObjectMap.find(ctx);
  if (itr == m_contextToObjectMap.end()) {
    return 0;
  } else {
    return (*itr).second;
  }
}
