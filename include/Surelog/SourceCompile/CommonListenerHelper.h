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
#include <Surelog/SourceCompile/VObjectTypes.h>

#include <map>
#include <string>
#include <string_view>

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
class VObject;

static constexpr char EscapeSequence[] = "#~@";

class CommonListenerHelper {
 public:
  virtual ~CommonListenerHelper() = default;

 public:
  FileContent* getFileContent() { return m_fileContent; }

 protected:
  virtual SymbolId registerSymbol(std::string_view symbol) = 0;

  NodeId NodeIdFromContext(const antlr4::tree::ParseTree* ctx) const;

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

  NodeId addVObject(antlr4::ParserRuleContext* ctx, std::string_view name,
                    VObjectType objtype);

  NodeId addVObject(antlr4::ParserRuleContext* ctx, VObjectType objtype);
  NodeId addVObject(antlr4::ParserRuleContext* ctx, SymbolId sym,
                    VObjectType objtype);

  void addParentChildRelations(NodeId indexParent,
                               antlr4::ParserRuleContext* ctx);

  NodeId getObjectId(antlr4::ParserRuleContext* ctx) const;

  virtual std::tuple<PathId, uint32_t, uint16_t, uint32_t, uint16_t>
  getFileLine(antlr4::ParserRuleContext* ctx, antlr4::Token* token) const = 0;

  NodeId& MutableChild(NodeId index);
  NodeId& MutableSibling(NodeId index);
  NodeId& MutableParent(NodeId index);

 protected:
  CommonListenerHelper(FileContent* file_content,
                       antlr4::CommonTokenStream* tokens)
      : m_fileContent(file_content), m_tokens(tokens) {}

  // These should be *const, but they are still set in some places.
  // TODO: fix these places.
  FileContent* m_fileContent;
  antlr4::CommonTokenStream* const m_tokens;

  typedef std::map<const antlr4::tree::ParseTree*, NodeId> ContextToObjectMap;
  ContextToObjectMap m_contextToObjectMap;
};

}  // namespace SURELOG

#endif /* SURELOG_COMMONLISTENERHELPER_H */
