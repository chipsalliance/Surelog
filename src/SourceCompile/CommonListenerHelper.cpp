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
 * File:   CommonListenerHelper.cpp
 * Author: alain
 *
 * Created on December 5, 2019, 9:13 PM
 */

#include <Surelog/Design/DesignElement.h>
#include <Surelog/Design/FileContent.h>
#include <Surelog/SourceCompile/CommonListenerHelper.h>
#include <Surelog/SourceCompile/SymbolTable.h>
#include <antlr4-runtime.h>

namespace SURELOG {

using namespace antlr4;

CommonListenerHelper::~CommonListenerHelper() {
  // TODO: ownership not clear
  // delete m_fileContent;
}

NodeId CommonListenerHelper::NodeIdFromContext(
    const antlr4::tree::ParseTree* ctx) const {
  auto found = m_contextToObjectMap.find(ctx);
  return (found == m_contextToObjectMap.end()) ? InvalidNodeId : found->second;
}

const VObject& CommonListenerHelper::Object(NodeId index) {
  return m_fileContent->Object(index);
}

NodeId CommonListenerHelper::UniqueId(NodeId index) const { return index; }

SymbolId CommonListenerHelper::Name(NodeId index) const {
  return m_fileContent->Name(index);
}

NodeId CommonListenerHelper::Child(NodeId index) const {
  return m_fileContent->Child(index);
}
NodeId& CommonListenerHelper::MutableChild(NodeId index) {
  return m_fileContent->MutableObject(index)->m_child;
}

NodeId CommonListenerHelper::Sibling(NodeId index) const {
  return m_fileContent->Sibling(index);
}
NodeId& CommonListenerHelper::MutableSibling(NodeId index) {
  return m_fileContent->MutableObject(index)->m_sibling;
}

NodeId CommonListenerHelper::Definition(NodeId index) const {
  return m_fileContent->Definition(index);
}

NodeId CommonListenerHelper::Parent(NodeId index) const {
  return m_fileContent->Parent(index);
}
NodeId& CommonListenerHelper::MutableParent(NodeId index) {
  return m_fileContent->MutableObject(index)->m_parent;
}

VObjectType CommonListenerHelper::Type(NodeId index) const {
  return m_fileContent->Type(index);
}

unsigned short CommonListenerHelper::Column(NodeId index) const {
  return m_fileContent->Column(index);
}

unsigned int CommonListenerHelper::Line(NodeId index) const {
  return m_fileContent->Line(index);
}

int CommonListenerHelper::addVObject(ParserRuleContext* ctx, SymbolId sym,
                                     VObjectType objtype) {
  SymbolId fileId;
  auto [line, column, endLine, endColumn] = getFileLine(ctx, fileId);

  NodeId objectIndex = m_fileContent->addObject(sym, fileId, objtype, line,
                                                column, endLine, endColumn);
  VObject* inserted = m_fileContent->MutableObject(objectIndex);
  m_contextToObjectMap.insert(std::make_pair(ctx, objectIndex));
  addParentChildRelations(objectIndex, ctx);
  std::vector<SURELOG::DesignElement*>& delements =
      m_fileContent->getDesignElements();
  for (auto it = delements.rbegin(); it != delements.rend(); ++it) {
    if ((*it)->m_context == ctx) {
      // Use the file and line number of the design object (package, module),
      // true file/line when splitting
      inserted->m_fileId = (*it)->m_fileId;
      inserted->m_line = (*it)->m_line;
      (*it)->m_node = NodeId(objectIndex);
      break;
    }
  }
  return objectIndex;
}

int CommonListenerHelper::addVObject(ParserRuleContext* ctx,
                                     std::string_view name,
                                     VObjectType objtype) {
  return addVObject(ctx, registerSymbol(name), objtype);
}

int CommonListenerHelper::addVObject(ParserRuleContext* ctx,
                                     VObjectType objtype) {
  return addVObject(ctx, BadSymbolId, objtype);
}

void CommonListenerHelper::addParentChildRelations(NodeId indexParent,
                                                   ParserRuleContext* ctx) {
  NodeId currentIndex = indexParent;
  for (tree::ParseTree* child : ctx->children) {
    NodeId childIndex = NodeIdFromContext(child);
    if (childIndex) {
      MutableParent(childIndex) = UniqueId(indexParent);
      if (indexParent == currentIndex) {
        MutableChild(indexParent) = UniqueId(childIndex);
      } else {
        MutableSibling(currentIndex) = UniqueId(childIndex);
      }
      currentIndex = childIndex;
    }
  }
}

NodeId CommonListenerHelper::getObjectId(ParserRuleContext* ctx) const {
  auto itr = m_contextToObjectMap.find(ctx);
  if (itr == m_contextToObjectMap.end()) {
    return InvalidNodeId;
  } else {
    return (*itr).second;
  }
}

}  // namespace SURELOG
