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

#include "Surelog/SourceCompile/CommonListenerHelper.h"

#include <antlr4-runtime.h>

#include <cstdint>
#include <string_view>
#include <vector>

#include "Surelog/Common/NodeId.h"
#include "Surelog/Common/SymbolId.h"
#include "Surelog/Design/DesignElement.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/SourceCompile/VObjectTypes.h"
#include "Surelog/Utils/StringUtils.h"

namespace SURELOG {

using antlr4::tree::ParseTree;

CommonListenerHelper::CommonListenerHelper(Session* session,
                                           FileContent* file_content,
                                           antlr4::CommonTokenStream* tokens)
    : m_session(session),
      m_fileContent(file_content),
      m_tokens(tokens),
      m_regexEscSeqReplace(kEscapeSequence),
      m_regexEscSeqSearch(StrCat(kEscapeSequence, "(.*?)", kEscapeSequence)),
      m_regexTranslateOn(R"(\/\/\s*(synopsys|pragma)\s+translate_on\s*)"),
      m_regexTranslateOff(R"(\/\/\s*(synopsys|pragma)\s+translate_off\s*)") {}

NodeId CommonListenerHelper::NodeIdFromContext(const ParseTree* tree) const {
  auto found = m_contextToObjectMap.find(tree);
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

uint16_t CommonListenerHelper::Column(NodeId index) const {
  return m_fileContent->Column(index);
}

uint32_t CommonListenerHelper::Line(NodeId index) const {
  return m_fileContent->Line(index);
}

NodeId CommonListenerHelper::addVObject(ParseTree* tree, SymbolId sym,
                                        VObjectType objtype,
                                        bool skipParenting /* = false */) {
  auto [fid, sl, sc, el, ec] = getFileLine(tree, nullptr);

  NodeId objectIndex =
      m_fileContent->addObject(sym, fid, objtype, sl, sc, el, ec);
  VObject* const inserted = m_fileContent->MutableObject(objectIndex);
  PathId ppFileId;
  std::tie(ppFileId, inserted->m_ppStartLine, inserted->m_ppStartColumn,
           inserted->m_ppEndLine, inserted->m_ppEndColumn) =
      getPPFileLine(tree, nullptr);
  addNodeIdForContext(tree, objectIndex);
  if (!skipParenting) addParentChildRelations(tree, objectIndex);
  std::vector<SURELOG::DesignElement*>& delements =
      m_fileContent->getDesignElements();
  for (auto it = delements.rbegin(); it != delements.rend(); ++it) {
    if ((*it)->m_context == tree) {
      // Use the file and line number of the design object (package, module),
      // true file/line when splitting
      inserted->m_fileId = (*it)->m_fileId;
      inserted->m_startLine = (*it)->m_startLine;
      inserted->m_endLine = (*it)->m_endLine;
      (*it)->m_node = NodeId(objectIndex);
      break;
    }
  }
  return objectIndex;
}

NodeId CommonListenerHelper::addVObject(ParseTree* tree, std::string_view name,
                                        VObjectType objtype,
                                        bool skipParenting /* = false */) {
  return addVObject(tree, registerSymbol(name), objtype, skipParenting);
}

NodeId CommonListenerHelper::addVObject(ParseTree* tree, VObjectType objtype,
                                        bool skipParenting /* = false */) {
  return addVObject(tree, BadSymbolId, objtype, skipParenting);
}

void CommonListenerHelper::addNodeIdForContext(const ParseTree* tree,
                                               NodeId nodeId) {
  auto [it, succeeded] = m_contextToObjectMap.emplace(tree, nodeId);
  if (!succeeded) {
    std::vector<VObject>& objects = *m_fileContent->mutableVObjects();
    NodeId tid = it->second;
    while (tid && objects[tid].m_sibling) {
      tid = objects[tid].m_sibling;
    }
    objects[tid].m_sibling = nodeId;
  }
}

void CommonListenerHelper::addParentChildRelations(const ParseTree* tree,
                                                   NodeId parentId) {
  std::vector<VObject>& objects = *m_fileContent->mutableVObjects();
  VObject& parent = objects[parentId];

  NodeId tailId = parentId;
  for (ParseTree* subtree : tree->children) {
    NodeId childId = NodeIdFromContext(subtree);
    while (childId) {
      VObject& child = objects[childId];
      child.m_parent = parentId;
      if (parentId == tailId) {
        parent.m_child = childId;
      } else {
        VObject& tail = objects[tailId];
        tail.m_sibling = childId;
      }
      tailId = childId;
      childId = child.m_sibling;
    }
  }
}
}  // namespace SURELOG
