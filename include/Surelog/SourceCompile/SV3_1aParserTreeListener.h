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
 * File:   SV3_1aParserTreeListener.h
 * Author: hs
 *
 * Created on January 31, 2023, 12:00 PM
 */

#ifndef SURELOG_SV3_1APARSERTREELISTENER_H
#define SURELOG_SV3_1APARSERTREELISTENER_H
#pragma once

#include <Surelog/SourceCompile/SV3_1aTreeShapeHelper.h>
#include <parser/SV3_1aParserBaseListener.h>

#include <map>
#include <optional>
#include <regex>
#include <tuple>
#include <vector>

namespace SURELOG {
class Session;

class SV3_1aParserTreeListener final : public SV3_1aParserBaseListener,
                                      public SV3_1aTreeShapeHelper {
  using vobjects_t = std::vector<VObject>;

  using visited_tokens_t = std::set<const antlr4::Token*>;
  using preproc_begin_statck_t = std::vector<antlr4::Token*>;

  using column_offset_t = std::pair<uint16_t, int32_t>;
  using offsets_t = std::multimap<uint32_t, column_offset_t>;

 public:
  SV3_1aParserTreeListener(Session* session, ParseFile* pf,
                          antlr4::CommonTokenStream* tokens,
                          uint32_t lineOffset, FileContent* ppFileContent);
  ~SV3_1aParserTreeListener() final = default;

  void enterString_value(SV3_1aParser::String_valueContext* ctx) final;

  void enterEveryRule(antlr4::ParserRuleContext* ctx) final;
  void exitEveryRule(antlr4::ParserRuleContext* ctx) final;
  void visitTerminal(antlr4::tree::TerminalNode* node) final;
  void visitErrorNode(antlr4::tree::ErrorNode* node) final;

 private:
  using SV3_1aTreeShapeHelper::addVObject;
  NodeId addVObject(antlr4::tree::TerminalNode* node, VObjectType objectType);

  NodeId mergeSubTree(NodeId ppNodeId);
  void mergeSubTrees(antlr4::tree::ParseTree* tree, NodeId ppNodeId);

  std::optional<bool> isUnaryOperator(
      const antlr4::tree::TerminalNode* node) const;

  void overrideLocation(NodeId nodeId, antlr4::Token* token);
  void applyLocationOffsets(VObject& object);
  void applyLocationOffsets();

  void visitPreprocBegin(antlr4::Token* token);
  void visitPreprocEnd(antlr4::Token* token, NodeId ppNodeId);
  void processPendingTokens(antlr4::tree::ParseTree* tree,
                            size_t endTokenIndex);

 private:
  FileContent* const m_ppFileContent = nullptr;
  offsets_t m_offsets;

  visited_tokens_t m_visitedTokens;
  preproc_begin_statck_t m_preprocBeginStack;

  size_t m_lastVisitedTokenIndex = 0;
  int32_t m_paused = 0;
  bool m_enteredSourceText = false;
};
}  // namespace SURELOG
#endif  // SURELOG_SV3_1APARSERTREELISTENER_H
