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
 * File:   SV3_1aParserTreeListener.cpp
 * Author: hs
 *
 * Created on January 31, 2023, 12:00 PM
 */

#include <Surelog/Design/Design.h>
#include <Surelog/Design/FileContent.h>
#include <Surelog/SourceCompile/CompileSourceFile.h>
#include <Surelog/SourceCompile/Compiler.h>
#include <Surelog/SourceCompile/ParseFile.h>
#include <Surelog/SourceCompile/SV3_1aParserTreeListener.h>
#include <Surelog/Utils/NumUtils.h>
#include <Surelog/Utils/ParseUtils.h>
#include <Surelog/Utils/StringUtils.h>
#include <parser/SV3_1aLexer.h>

#include <algorithm>
#include <iomanip>

namespace SURELOG {
SV3_1aParserTreeListener::SV3_1aParserTreeListener(
    Session *session, ParseFile *pf, antlr4::CommonTokenStream *tokens,
    uint32_t lineOffset, FileContent *ppFileContent)
    : SV3_1aTreeShapeHelper(session, pf, tokens, lineOffset),
      m_ppFileContent(ppFileContent) {
  if (m_pf->getFileContent() == nullptr) {
    m_fileContent = new FileContent(session, m_pf->getFileId(0),
                                    m_pf->getLibrary(), nullptr, BadPathId);
    m_pf->setFileContent(m_fileContent);
  } else {
    m_fileContent = m_pf->getFileContent();
  }
}

NodeId SV3_1aParserTreeListener::addVObject(antlr4::tree::TerminalNode *node,
                                            VObjectType objectType) {
  // This call connect the node to the tree i.e. parenting and shouldn't
  // be replaced with node->getSymbol() as second argument. Also, the
  // returned id doesn't get collected in orphans and so parenting gets
  // entirely ignored if called with getSymbol() as argument.
  return (m_paused == 0) ? addVObject(node, node->getText(), objectType)
                         : InvalidNodeId;
}

NodeId SV3_1aParserTreeListener::mergeSubTree(NodeId ppNodeId) {
  const vobjects_t &ppObjects = m_ppFileContent->getVObjects();
  const VObject &ppObject = ppObjects[ppNodeId];

  vobjects_t &objects = *m_fileContent->mutableVObjects();

  NodeId firstChildId;
  NodeId lastChildId;
  NodeId ppChildId = ppObject.m_child;
  while (ppChildId) {
    NodeId childId = mergeSubTree(ppChildId);
    if (firstChildId) {
      objects[lastChildId].m_sibling = childId;
    } else {
      firstChildId = childId;
    }
    lastChildId = childId;
    ppChildId = ppObjects[ppChildId].m_sibling;
  }

  NodeId nodeId = m_fileContent->addObject(
      ppObject.m_name, ppObject.m_fileId, ppObject.m_type, ppObject.m_startLine,
      ppObject.m_startColumn, ppObject.m_endLine, ppObject.m_endColumn);
  VObject &inserted = objects[nodeId];
  inserted.m_ppStartLine = ppObject.m_startLine;
  inserted.m_ppStartColumn = ppObject.m_startColumn;
  inserted.m_ppEndLine = ppObject.m_endLine;
  inserted.m_ppEndColumn = ppObject.m_endColumn;

  if (firstChildId) {
    VObject &object = objects[nodeId];
    object.m_child = firstChildId;

    NodeId childId = firstChildId;
    while (childId) {
      objects[childId].m_parent = nodeId;
      childId = objects[childId].m_sibling;
    }
  }

  return nodeId;
}

void SV3_1aParserTreeListener::mergeSubTrees(antlr4::tree::ParseTree *tree,
                                             NodeId ppNodeId) {
  const vobjects_t &ppObjects = m_ppFileContent->getVObjects();
  for (NodeId ppChildNodeId = ppObjects[ppNodeId].m_child; ppChildNodeId;
       ppChildNodeId = ppObjects[ppChildNodeId].m_sibling) {
    addNodeIdForContext(tree, mergeSubTree(ppChildNodeId));
  }
}

std::optional<bool> SV3_1aParserTreeListener::isUnaryOperator(
    const antlr4::tree::TerminalNode *node) const {
  switch (((antlr4::ParserRuleContext *)node->parent)->getRuleIndex()) {
    case SV3_1aParser::RuleExpression: {
      SV3_1aParser::ExpressionContext *ctx =
          (SV3_1aParser::ExpressionContext *)node->parent;
      return std::optional<bool>(ctx->expression().size() == 1);
    } break;

    case SV3_1aParser::RuleConstant_expression: {
      SV3_1aParser::Constant_expressionContext *ctx =
          (SV3_1aParser::Constant_expressionContext *)node->parent;
      return std::optional<bool>(ctx->constant_primary() != nullptr);
    } break;

    default:
      break;
  }

  return std::optional<bool>();
}

void SV3_1aParserTreeListener::enterString_value(
    SV3_1aParser::String_valueContext *ctx) {
  if (m_paused != 0) return;

  std::string text = ctx->String()->getText();

  std::smatch match;
  while (std::regex_search(text, match, m_regexEscSeqSearch)) {
    std::string var = "\\" + match[1].str();
    text = text.replace(match.position(0), match.length(0), var);
  }

  addVObject(ctx, text, VObjectType::paString_value);
  m_visitedTokens.emplace(ctx->String()->getSymbol());

  if (text.size() > SV_MAX_STRING_SIZE) {
    logError(ErrorDefinition::PA_MAX_LENGTH_IDENTIFIER, ctx, text);
  }
}

void SV3_1aParserTreeListener::overrideLocation(NodeId nodeId,
                                                antlr4::Token *token) {
  VObject *const object = m_fileContent->MutableObject(nodeId);
  std::tie(object->m_fileId, object->m_startLine, object->m_startColumn,
           object->m_endLine, object->m_endColumn) =
      getFileLine(nullptr, token);
  std::tie(object->m_ppStartLine, object->m_ppStartColumn) =
      ParseUtils::getLineColumn(token);
  std::tie(object->m_ppEndLine, object->m_ppEndColumn) =
      ParseUtils::getEndLineColumn(token);
}

void SV3_1aParserTreeListener::applyLocationOffsets(VObject &object) {
  uint16_t sc = object.m_startColumn;
  uint16_t scpivot = 0;
  std::pair<offsets_t::const_iterator, offsets_t::const_iterator> slItBounds =
      m_offsets.equal_range(object.m_startLine);
  for (offsets_t::const_iterator it = slItBounds.first; it != slItBounds.second;
       ++it) {
    if ((object.m_startColumn >= it->second.first) &&
        (it->second.first > scpivot)) {
      sc = object.m_startColumn - it->second.second;
      scpivot = it->second.first;
    }
  }
  object.m_startColumn = sc;

  uint16_t ec = object.m_endColumn;
  uint16_t ecpivot = 0;
  std::pair<offsets_t::const_iterator, offsets_t::const_iterator> elItBounds =
      m_offsets.equal_range(object.m_endLine);
  for (offsets_t::const_iterator it = elItBounds.first; it != elItBounds.second;
       ++it) {
    if ((object.m_endColumn >= it->second.first) &&
        (it->second.first > ecpivot)) {
      ec = object.m_endColumn - it->second.second;
      ecpivot = it->second.first;
    }
  }
  object.m_endColumn = ec;
}

void SV3_1aParserTreeListener::applyLocationOffsets() {
  // std::cout << "ParserTreeListener::ColumnOffsets:" << std::endl;
  // for (const auto &entry : m_offsets) {
  //   std::cout << std::setfill(' ') << std::setw(4) << entry.first
  //             << std::setfill(' ') << std::setw(4) <<
  //             std::get<0>(entry.second)
  //             << std::setfill(' ') << std::setw(4) <<
  //             std::get<1>(entry.second)
  //             << std::endl;
  // }
  // std::cout << std::endl;

  vobjects_t &vobjects = *m_fileContent->mutableVObjects();
  for (vobjects_t::reference object : vobjects) {
    if (static_cast<int32_t>(object.m_type) <
        static_cast<int32_t>(VObjectType::paIndexBegin)) {
      continue;  // Don't apply offsets to ppXXXX types
    }

    if (object.m_type == VObjectType::paTop_level_rule) {
      // HACK(HS): For some unknown reason, the top level rule doesn't start
      // at the top of the file and instead starts at where the module (or
      // whatever is in channel 0). Force it to start at 1, 1 so the
      // validation check can pass.
      object.m_startLine = 1;
      object.m_startColumn = 1;
    }

    applyLocationOffsets(object);
  }
}

void SV3_1aParserTreeListener::visitPreprocBegin(antlr4::Token *token) {
  m_preprocBeginStack.emplace_back(token);
  ++m_paused;
}

void SV3_1aParserTreeListener::visitPreprocEnd(antlr4::Token *token,
                                               NodeId ppNodeId) {
  antlr4::Token *const endToken = token;
  antlr4::Token *const beginToken = m_preprocBeginStack.back();
  m_preprocBeginStack.pop_back();

  const LineColumn bslc = ParseUtils::getLineColumn(beginToken);
  const LineColumn belc = ParseUtils::getEndLineColumn(beginToken);

  const LineColumn eslc = ParseUtils::getLineColumn(endToken);
  const LineColumn eelc = ParseUtils::getEndLineColumn(endToken);

  const auto [sfid, bsl, bsc, bel, bec] = getFileLine(nullptr, beginToken);
  const auto [efid, esl, esc, eel, eec] = getFileLine(nullptr, endToken);

  if ((bslc.first == bsl) && (bslc.second == bsc) && (belc.first == bel) &&
      (belc.second == bec) && (eslc.first == esl) && (eslc.second == esc) &&
      (eelc.first == eel) && (eelc.second == eec) &&
      (bslc.first == eelc.first)) {
    m_offsets.emplace(std::piecewise_construct, std::forward_as_tuple(eel),
                      std::forward_as_tuple(eec, (bec - bsc) + (eec - esc)));
  } else {
    m_offsets.emplace(std::piecewise_construct, std::forward_as_tuple(eel),
                      std::forward_as_tuple(eec, eec - esc));
  }
  --m_paused;
}

void SV3_1aParserTreeListener::processPendingTokens(
    antlr4::tree::ParseTree *tree, size_t endTokenIndex) {
  if (!m_enteredSourceText) {
    return;  // Wait until the source_text rule is visited!
  }

  while ((m_lastVisitedTokenIndex < endTokenIndex) &&
         (m_lastVisitedTokenIndex < m_tokens->size())) {
    antlr4::Token *const lastToken = m_tokens->get(m_lastVisitedTokenIndex);
    ++m_lastVisitedTokenIndex;

    switch (lastToken->getType()) {
      case SV3_1aParser::PREPROC_BEGIN: {
        visitPreprocBegin(lastToken);
      } break;

      case SV3_1aParser::PREPROC_END: {
        const std::string text = lastToken->getText();
        std::string_view svtext = text;
        svtext.remove_prefix(kPreprocEndPrefix.length());

        uint32_t index = 0;
        if (NumUtils::parseUint32(svtext, &index)) {
          const NodeId ppParentNodeId(index);
          mergeSubTrees(tree, ppParentNodeId);
          visitPreprocEnd(lastToken, ppParentNodeId);
        }
      } break;

      case SV3_1aParser::One_line_comment: {
        if (m_paused != 0) break;

        std::string text = lastToken->getText();

        bool hasCR = false;
        std::string_view trimmed = text;
        if (!trimmed.empty() && (trimmed.back() == '\n')) {
          trimmed.remove_suffix(1);
          hasCR = true;
        }

        if (!trimmed.empty()) {
          const NodeId nodeId =
              addVObject(tree, trimmed, VObjectType::paOne_line_comment, true);
          overrideLocation(nodeId, lastToken);

          VObject *const object = m_fileContent->MutableObject(nodeId);
          if (hasCR) {
            --object->m_endLine;
            object->m_endColumn = object->m_startColumn + trimmed.length();

            --object->m_ppEndLine;
            object->m_ppEndColumn = object->m_ppStartColumn + trimmed.length();
          }
        }

        if (hasCR) {
          const NodeId nodeId = addVObject(tree, "\n", VObjectType::ppCR, true);
          overrideLocation(nodeId, lastToken);

          VObject *const object = m_fileContent->MutableObject(nodeId);
          object->m_startColumn += trimmed.length();
          object->m_ppStartColumn += trimmed.length();
          applyLocationOffsets(*object);
        }

        m_visitedTokens.emplace(lastToken);
      } break;

      case SV3_1aParser::Block_comment: {
        if (m_paused != 0) break;

        const NodeId nodeId = addVObject(tree, lastToken->getText(),
                                         VObjectType::paBlock_comment, true);
        overrideLocation(nodeId, lastToken);
      } break;

      case SV3_1aParser::White_space: {
        if (m_paused != 0) break;

        std::string text = lastToken->getText();
        auto [fid, sl, sc, el, ec] = getFileLine(nullptr, lastToken);
        LineColumn lc = ParseUtils::getLineColumn(lastToken);
        for (std::string_view part : StringUtils::splitLines(text)) {
          bool hasCR = false;
          if (!part.empty() && (part.back() == '\n')) {
            part.remove_suffix(1);
            hasCR = true;
          }
          if (!part.empty()) {
            const NodeId nodeId =
                addVObject(tree, part, VObjectType::paWhite_space, true);
            VObject *const object = m_fileContent->MutableObject(nodeId);

            object->m_ppStartLine = object->m_ppEndLine = lc.first;
            object->m_ppStartColumn = lc.second;
            object->m_ppEndLine = lc.first;
            object->m_ppEndColumn = lc.second += part.length();

            object->m_startLine = object->m_endLine = sl;
            object->m_startColumn = sc;
            object->m_endColumn = sc += part.length();
          }
          if (hasCR) {
            const NodeId nodeId =
                addVObject(tree, "\n", VObjectType::ppCR, true);
            VObject *const object = m_fileContent->MutableObject(nodeId);

            object->m_ppStartLine = lc.first;
            object->m_ppStartColumn = lc.second;
            object->m_ppEndLine = ++lc.first;
            object->m_ppEndColumn = lc.second = 1;

            object->m_startLine = object->m_endLine = sl;
            object->m_startColumn = sc;
            object->m_endLine = ++sl;
            object->m_endColumn = sc = 1;
            applyLocationOffsets(*object);
          }
        }
        m_visitedTokens.emplace(lastToken);
      } break;

      default:
        break;
    }
  }
}

void SV3_1aParserTreeListener::enterEveryRule(antlr4::ParserRuleContext *ctx) {
  if (const antlr4::Token *const startToken = ctx->getStart()) {
    // NOTE(HS): Bit of ambiguity here!
    // Should we append the nodes between two rules to the previous
    // or the current rule? If appended to the previous, they will show up
    // at the tail and if appended to current, they show up at head.
    // Either way, dependent on the source context, one of the other might
    // be more meaningful, and thus ambigious.
    processPendingTokens(ctx, startToken->getTokenIndex());
  }
  if (ctx->getRuleIndex() == SV3_1aParser::RuleSource_text) {
    m_enteredSourceText = true;
  }
}

void SV3_1aParserTreeListener::exitEveryRule(antlr4::ParserRuleContext *ctx) {
  bool shouldAddVObject = m_paused == 0;
  if (!shouldAddVObject) {
    for (const antlr4::tree::ParseTree *child : ctx->children) {
      if (NodeIdFromContext(child)) {
        shouldAddVObject = true;
        break;
      }
    }
  }
  if (!shouldAddVObject) return;

  // clang-format off
  if (shouldAddVObject) {
    switch (ctx->getRuleIndex()) {
<RULE_CASE_STATEMENTS>
      default: break;
    }
  }
  // clang-format on

  if (const antlr4::Token *const stopToken = ctx->getStop()) {
    if (!ctx->children.empty()) {
      processPendingTokens(ctx->children.back(), stopToken->getTokenIndex());
    }
  }

  if (ctx->getRuleIndex() == SV3_1aParser::RuleSource_text) {
    processPendingTokens(ctx, m_tokens->size());
    m_enteredSourceText = false;
  } else if (ctx->getRuleIndex() == SV3_1aParser::RuleTop_level_rule) {
    applyLocationOffsets();
  }
}

void SV3_1aParserTreeListener::visitTerminal(antlr4::tree::TerminalNode *node) {
  // Skip any tokens that are already handled as part of enterXXX/exitXXX rules
  const antlr4::Token *const token = node->getSymbol();
  if (token->getType() == antlr4::Token::EOF) return;
  if (!m_visitedTokens.emplace(token).second) return;

  processPendingTokens(node, token->getTokenIndex());
  if (m_paused != 0) return;

  // clang-format off
  NodeId nodeId;
  switch (token->getType()) {
    case SV3_1aParser::Escaped_identifier: {
      std::string text = node->getText();
      std::smatch match;
      while (std::regex_search(text, match, m_regexEscSeqSearch)) {
        std::string var = "\\" + match[1].str();
        text = text.replace(match.position(0), match.length(0), var);
      }
      nodeId = addVObject(node, text, VObjectType::paEscaped_identifier);
    } break;

<VISIT_CASE_STATEMENTS>
    default: break;
  }
  // clang-format on

  if (nodeId) {
    VObject *const object = m_fileContent->MutableObject(nodeId);

    const std::optional<bool> isUnary = isUnaryOperator(node);
    if (isUnary) {
      // clang-format off
      switch (token->getType()) {
        case SV3_1aParser::BITW_AND: object->m_type = isUnary.value() ? VObjectType::paUnary_BitwAnd : VObjectType::paBinOp_BitwAnd; break;
        case SV3_1aParser::BITW_OR: object->m_type = isUnary.value() ? VObjectType::paUnary_BitwOr : VObjectType::paBinOp_BitwOr; break;
        case SV3_1aParser::BITW_XOR: object->m_type = isUnary.value() ? VObjectType::paUnary_BitwXor : VObjectType::paBinOp_BitwXor; break;
        case SV3_1aParser::MINUS: object->m_type = isUnary.value() ? VObjectType::paUnary_Minus : VObjectType::paBinOp_Minus; break;
        case SV3_1aParser::PLUS: object->m_type = isUnary.value() ? VObjectType::paUnary_Plus : VObjectType::paBinOp_Plus; break;
        case SV3_1aParser::REDUCTION_NAND: object->m_type = isUnary.value() ? VObjectType::paUnary_ReductNand : VObjectType::paBinOp_ReductNand; break;
        case SV3_1aParser::REDUCTION_XNOR1: object->m_type = isUnary.value() ? VObjectType::paUnary_ReductXnor1 : VObjectType::paBinOp_ReductXnor1; break;
        case SV3_1aParser::REDUCTION_XNOR2: object->m_type = isUnary.value() ? VObjectType::paUnary_ReductXnor2 : VObjectType::paBinOp_ReductXnor2; break;
        case SV3_1aParser::STAR: object->m_type = VObjectType::paBinOp_Mult; break;
        default: break;
      }
      // clang-format on
    }
  }
}

void SV3_1aParserTreeListener::visitErrorNode(antlr4::tree::ErrorNode *node) {
  if (node->getText().find("<missing ") != 0) {
    addVObject(node, VObjectType::slUnparsable_Text);
  }
}
}  // namespace SURELOG
