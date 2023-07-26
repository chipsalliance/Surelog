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
 * File:   SV3_1aParseTreeListener.h
 * Author: hs
 *
 * Created on January 31, 2023, 12:00 PM
 */

#ifndef SURELOG_SV3_1APARSETREELISTENER_H
#define SURELOG_SV3_1APARSETREELISTENER_H
#pragma once

#include <Surelog/SourceCompile/SV3_1aTreeShapeHelper.h>
#include <parser/SV3_1aParserBaseListener.h>

#include <optional>
#include <regex>
#include <vector>

namespace SURELOG {
class SV3_1aParseTreeListener final : public SV3_1aParserBaseListener,
                                      public SV3_1aTreeShapeHelper {
 public:
  SV3_1aParseTreeListener(FileContent* ppFileContent,
                          ParseFile* pf, antlr4::CommonTokenStream* tokens,
                          unsigned int lineOffset);
  virtual ~SV3_1aParseTreeListener() override = default;

  void enterString_value(SV3_1aParser::String_valueContext* ctx) final;

  void exitEveryRule(antlr4::ParserRuleContext* ctx) final;
  void visitTerminal(antlr4::tree::TerminalNode* node) final;
  void visitErrorNode(antlr4::tree::ErrorNode* node) final;

 private:
  using SV3_1aTreeShapeHelper::addVObject;
  NodeId addVObject(antlr4::ParserRuleContext* ctx, antlr4::Token* token,
                    VObjectType objtype);
  NodeId addVObject(antlr4::tree::TerminalNode* node, VObjectType objtype);

  NodeId mergeObjectTree(const VObject& object);
  std::optional<bool> isUnaryOperator(const antlr4::tree::TerminalNode* node) const;
  void applyColumnOffsets(NodeId nodeId) const;

 private:
  typedef std::map<int32_t, std::vector<std::pair<int32_t, int32_t>>>
      column_offsets_t;

  FileContent* const m_ppFileContent;
  std::set<const antlr4::Token*> m_visited;
  const std::regex m_escapeSequenceRegex;
  column_offsets_t m_columnOffsets;
};
}  // namespace SURELOG
#endif  // SURELOG_SV3_1APARSETREELISTENER_H
