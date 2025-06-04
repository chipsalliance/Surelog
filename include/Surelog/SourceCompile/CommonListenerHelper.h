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

#ifndef SURELOG_COMMONLISTENERHELPER_H
#define SURELOG_COMMONLISTENERHELPER_H
#pragma once

#include <Surelog/Common/NodeId.h>
#include <Surelog/Common/PathId.h>
#include <Surelog/Common/SymbolId.h>
#include <Surelog/SourceCompile/VObjectTypes.h>

#include <cstdint>
#include <map>
#include <regex>
#include <string>
#include <string_view>
#include <tuple>

namespace antlr4 {
class CommonTokenStream;
class ParserRuleContext;
class Token;

namespace tree {
class ParseTree;
}
}  // namespace antlr4

namespace SURELOG {
class FileContent;
class Session;
class VObject;

static constexpr char kEscapeSequence[] = "#~@";

static constexpr std::string_view kPreprocBeginPrefix = "{!< ";
static constexpr std::string_view kPreprocBeginSuffix = " !}";

static constexpr std::string_view kPreprocEndPrefix = "{! ";
static constexpr std::string_view kPreprocEndSuffix = " >!}";

class CommonListenerHelper {
 public:
  virtual ~CommonListenerHelper() = default;

 public:
  FileContent* getFileContent() { return m_fileContent; }
  const FileContent* getFileContent() const { return m_fileContent; }

 protected:
  virtual SymbolId registerSymbol(std::string_view symbol) = 0;

  NodeId NodeIdFromContext(const antlr4::tree::ParseTree* tree) const;

  const VObject& Object(NodeId index);

  NodeId UniqueId(NodeId index) const;

  SymbolId Name(NodeId index) const;
  NodeId Child(NodeId index) const;
  NodeId Sibling(NodeId index) const;
  NodeId Parent(NodeId index) const;
  NodeId Definition(NodeId index) const;
  VObjectType Type(NodeId index) const;
  uint16_t Column(NodeId index) const;
  uint32_t Line(NodeId index) const;

  NodeId addVObject(antlr4::tree::ParseTree* tree, std::string_view name,
                    VObjectType objtype, bool skipParenting = false);
  NodeId addVObject(antlr4::tree::ParseTree* tree, VObjectType objtype,
                    bool skipParenting = false);
  NodeId addVObject(antlr4::tree::ParseTree* tree, SymbolId sym,
                    VObjectType objtype, bool skipParenting = false);

  void addNodeIdForContext(const antlr4::tree::ParseTree* tree, NodeId nodeId);
  void addParentChildRelations(const antlr4::tree::ParseTree* tree,
                               NodeId parentId);

  virtual std::tuple<PathId, uint32_t, uint16_t, uint32_t, uint16_t>
  getPPFileLine(antlr4::tree::ParseTree* tree, antlr4::Token* token) const = 0;
  virtual std::tuple<PathId, uint32_t, uint16_t, uint32_t, uint16_t>
  getFileLine(antlr4::tree::ParseTree* tree, antlr4::Token* token) const = 0;

  NodeId& MutableChild(NodeId index);
  NodeId& MutableSibling(NodeId index);
  NodeId& MutableParent(NodeId index);

 protected:
  CommonListenerHelper(Session* session, FileContent* file_content,
                       antlr4::CommonTokenStream* tokens);

 protected:
  using ContextToObjectMap = std::map<const antlr4::tree::ParseTree*, NodeId>;
  Session* const m_session = nullptr;

  // These should be *const, but they are still set in some places.
  // TODO: fix these places.
  FileContent* m_fileContent = nullptr;
  antlr4::CommonTokenStream* const m_tokens = nullptr;

  ContextToObjectMap m_contextToObjectMap;
  const std::regex m_regexEscSeqReplace;
  const std::regex m_regexEscSeqSearch;
  const std::regex m_regexTranslateOn;
  const std::regex m_regexTranslateOff;
};

}  // namespace SURELOG

#endif /* SURELOG_COMMONLISTENERHELPER_H */
