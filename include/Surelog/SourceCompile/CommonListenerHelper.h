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
#include <Surelog/SourceCompile/VObjectTypes.h>

#include <map>
#include <string>

namespace antlr4 {
class CommonTokenStream;
class ParserRuleContext;
namespace tree {
class ParseTree;
}
}  // namespace antlr4

namespace SURELOG {

class FileContent;
class SymbolId;
class VObject;

static constexpr char EscapeSequence[] = "#~@";

class CommonListenerHelper {
 public:
  virtual ~CommonListenerHelper();

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
  unsigned short Column(NodeId index) const;
  unsigned int Line(NodeId index) const;

  int addVObject(antlr4::ParserRuleContext* ctx, std::string_view name,
                 VObjectType objtype);

  int addVObject(antlr4::ParserRuleContext* ctx, VObjectType objtype);

  void addParentChildRelations(NodeId indexParent,
                               antlr4::ParserRuleContext* ctx);

  NodeId getObjectId(antlr4::ParserRuleContext* ctx) const;

  FileContent* getFileContent() { return m_fileContent; }

  virtual std::tuple<unsigned int, unsigned short, unsigned int, unsigned short>
  getFileLine(antlr4::ParserRuleContext* ctx, SymbolId& fileId) = 0;

 private:
  NodeId& MutableChild(NodeId index);
  NodeId& MutableSibling(NodeId index);
  NodeId& MutableParent(NodeId index);

  int addVObject(antlr4::ParserRuleContext* ctx, SymbolId sym,
                 VObjectType objtype);

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
