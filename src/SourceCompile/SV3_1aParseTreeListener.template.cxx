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
 * File:   SV3_1aParseTreeListener.cpp
 * Author: hs
 *
 * Created on January 31, 2023, 12:00 PM
 */

#include <Surelog/Design/Design.h>
#include <Surelog/Design/FileContent.h>
#include <Surelog/SourceCompile/Compiler.h>
#include <Surelog/SourceCompile/CompileSourceFile.h>
#include <Surelog/SourceCompile/ParseFile.h>
#include <Surelog/SourceCompile/SV3_1aParseTreeListener.h>
#include <Surelog/Utils/ParseUtils.h>
#include <Surelog/Utils/NumUtils.h>

namespace SURELOG {
SV3_1aParseTreeListener::SV3_1aParseTreeListener(
    FileContent *ppFileContent, ParseFile *pf,
    antlr4::CommonTokenStream *tokens, unsigned int lineOffset)
    : SV3_1aTreeShapeHelper(pf, tokens, lineOffset),
      m_ppFileContent(ppFileContent),
      m_escapeSequenceRegex(
          std::string(EscapeSequence).append("(.*?)").append(EscapeSequence)) {
  if (m_pf->getFileContent() == nullptr) {
    m_fileContent = new FileContent(
        m_pf->getFileId(0), m_pf->getLibrary(),
        m_pf->getCompileSourceFile()->getSymbolTable(),
        m_pf->getCompileSourceFile()->getErrorContainer(), nullptr, BadPathId);
    m_pf->setFileContent(m_fileContent);
    // m_pf->getCompileSourceFile()->getCompiler()->getDesign()->addFileContent(
    //     m_pf->getFileId(0), m_fileContent);
  } else {
    m_fileContent = m_pf->getFileContent();
  }
}

NodeId SV3_1aParseTreeListener::addVObject(antlr4::ParserRuleContext *ctx,
                                           antlr4::Token *token,
                                           VObjectType objtype) {
  if (!m_visited.insert(token).second) return InvalidNodeId;

  auto [fileId, line, column, endLine, endColumn] = getFileLine(nullptr, token);
  const std::string name = token->getText();

  NodeId objectIndex = m_fileContent->addObject(
      registerSymbol(name), fileId, objtype, line, column, endLine, endColumn);

  NodeId parentIndex = NodeIdFromContext(ctx);
  m_fileContent->MutableObject(objectIndex)->m_parent = parentIndex;

  NodeId lastChild = m_fileContent->Child(parentIndex);
  if (lastChild) {
    NodeId nextSibling;
    while (nextSibling = m_fileContent->Sibling(lastChild)) {
      lastChild = nextSibling;
    }
    m_fileContent->MutableObject(lastChild)->m_sibling = objectIndex;
  } else {
    m_fileContent->MutableObject(parentIndex)->m_child = objectIndex;
  }
  return objectIndex;
}

NodeId SV3_1aParseTreeListener::addVObject(antlr4::tree::TerminalNode *node,
                                           VObjectType objtype) {
  if (NodeId nodeId = addVObject((antlr4::ParserRuleContext *)node, node->getText(), objtype)) {
    applyColumnOffsets(nodeId);
    return nodeId;
  }
  return InvalidNodeId;
}

NodeId SV3_1aParseTreeListener::mergeObjectTree(const VObject &object) {
  const std::vector<VObject> &ppObjects = m_ppFileContent->getVObjects();

  NodeId childId;
  if (object.m_child) {
    childId = mergeObjectTree(ppObjects[object.m_child]);
  }

  NodeId siblingId;
  if (object.m_sibling) {
    siblingId = mergeObjectTree(ppObjects[object.m_sibling]);
  }

  NodeId nodeId = m_fileContent->addObject(
      object.m_name, object.m_fileId, object.m_type, object.m_line,
      object.m_column, object.m_endLine, object.m_endColumn);
  VObject *const pObject = m_fileContent->MutableObject(nodeId);
  pObject->m_child = childId;
  pObject->m_sibling = siblingId;

  NodeId id = childId;
  while (id) {
    m_fileContent->MutableObject(id)->m_parent = nodeId;
    id = m_fileContent->Sibling(id);
  }

  return nodeId;
}

std::optional<bool> SV3_1aParseTreeListener::isUnaryOperator(
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

void SV3_1aParseTreeListener::applyColumnOffsets(NodeId nodeId) const {
  if (!nodeId || m_columnOffsets.empty()) return;
  if (VObject *const object = m_fileContent->MutableObject(nodeId)) {
    const int32_t ppColumn = static_cast<int32_t>(object->m_column);
    column_offsets_t::const_iterator it1 = m_columnOffsets.find(object->m_line);
    if (it1 != m_columnOffsets.end()) {
      int32_t column = ppColumn;
      for (typename column_offsets_t::mapped_type::const_reference pair :
           it1->second) {
        if (pair.first < ppColumn) {
          column += pair.second;
        }
      }
      object->m_column = static_cast<uint16_t>(column);
    }

    const int32_t ppEndColumn = static_cast<int32_t>(object->m_endColumn);
    column_offsets_t::const_iterator it2 = m_columnOffsets.find(object->m_endLine);
    if (it2 != m_columnOffsets.end()) {
      int32_t endColumn = ppEndColumn;
      for (typename column_offsets_t::mapped_type::const_reference pair :
           it2->second) {
        if (pair.first < ppEndColumn) {
          endColumn += pair.second;
        }
      }
      object->m_endColumn = static_cast<uint16_t>(endColumn);
    }
  }
}

void SV3_1aParseTreeListener::enterString_value(
    SV3_1aParser::String_valueContext *ctx) {
  std::string text = ctx->String()->getText();

  std::smatch match;
  while (std::regex_search(text, match, m_escapeSequenceRegex)) {
    std::string var = "\\" + match[1].str();
    text = text.replace(match.position(0), match.length(0), var);
  }

  if (NodeId nodeId = addVObject(ctx, text, VObjectType::slString_value)) {
    applyColumnOffsets(nodeId);
  }
  m_visited.insert(ctx->String()->getSymbol());

  if (text.size() > SV_MAX_STRING_SIZE) {
    logError(ErrorDefinition::PA_MAX_LENGTH_IDENTIFIER, ctx, text);
  }
}

void SV3_1aParseTreeListener::exitEveryRule(antlr4::ParserRuleContext *ctx) {
  NodeId nodeId;

  // clang-format off
  switch (ctx->getRuleIndex()) {
<RULE_CASE_STATEMENTS>
    default: break;
  }
  // clang-format on

  if (nodeId) applyColumnOffsets(nodeId);

  const antlr4::Token *start = ctx->getStart();
  const antlr4::Token *stop = ctx->getStop();

  if ((ctx->getRuleIndex() == SV3_1aParser::RuleNull_rule) ||
      (start == nullptr) || (stop == nullptr)) {
    return;
  }

  // When processing source_text, go thru' all the tokens. The ones outside of any
  // meaningful rules aren't getting covererd because of the hidden channel logic.
  const size_t startIndex =
      (ctx->getRuleIndex() == SV3_1aParser::RuleSource_text)
          ? 0
          : start->getTokenIndex();
  const size_t stopIndex =
      (ctx->getRuleIndex() == SV3_1aParser::RuleSource_text)
          ? (m_tokens->size() - 1)
          : stop->getTokenIndex();

  for (size_t i = startIndex; i <= stopIndex; ++i) {
    antlr4::Token *const token = m_tokens->get(i);

    switch (token->getType()) {
      case SV3_1aParser::One_line_comment: {
        nodeId = addVObject(ctx, token, VObjectType::slOne_line_comment);
      } break;

      case SV3_1aParser::Block_comment: {
        nodeId = addVObject(ctx, token, VObjectType::slBlock_comment);
      } break;

      case SV3_1aParser::White_space: {
        nodeId = addVObject(ctx, token, VObjectType::slWhitespace);
      } break;

      default: {
        nodeId = InvalidNodeId;
      } break;
    }

    if (nodeId) applyColumnOffsets(nodeId);
  }
}

void SV3_1aParseTreeListener::visitTerminal(antlr4::tree::TerminalNode *node) {
  // Skip any tokens that are already handled as part of enterXXX/exitXXX rules
  const antlr4::Token *const token = node->getSymbol();
  if (token->getType() == antlr4::Token::EOF) return;
  if (!m_visited.insert(token).second) return;

  NodeId nodeId;
  const ParseUtils::LineColumn startLineColumn = ParseUtils::getLineColumn(node);
  const ParseUtils::LineColumn endLineColumn = ParseUtils::getEndLineColumn(node);

  // clang-format off
  switch (token->getType()) {
    case SV3_1aParser::Preproc_identifier: {
      const std::string text = token->getText();
      std::string_view svtext = text;
      svtext.remove_prefix(3);

      uint32_t index = 0;
      if (NumUtils::parseUint32(svtext, &index)) {
        const VObject &object = m_ppFileContent->getVObjects()[index];
        if (NodeId insertedNodeId = mergeObjectTree(object)) {
          m_contextToObjectMap.emplace(node, insertedNodeId);

          if (object.m_type == VObjectType::slMacro_instance) {
            const int32_t len = static_cast<int32_t>(object.m_endColumn)
              - static_cast<int32_t>(object.m_column);
            const int32_t ppLen = static_cast<int32_t>(endLineColumn.second)
              - static_cast<int32_t>(startLineColumn.second);

            column_offsets_t::iterator it = m_columnOffsets.find(startLineColumn.first);
            if (it == m_columnOffsets.end()) {
              it = m_columnOffsets.emplace(startLineColumn.first, column_offsets_t::mapped_type()).first;
            }
            it->second.emplace_back(static_cast<int32_t>(startLineColumn.second), len - ppLen);
          }
        }
      }
    } break;
    case SV3_1aParser::Escaped_identifier: {
      std::string text = node->getText();
      std::smatch match;
      while (std::regex_search(text, match, m_escapeSequenceRegex)) {
        std::string var = "\\" + match[1].str();
        text = text.replace(match.position(0), match.length(0), var);
      }
      nodeId = addVObject((antlr4::ParserRuleContext *)node, text, VObjectType::slEscaped_identifier);
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
        case SV3_1aParser::BITW_AND: object->m_type = isUnary.value() ? VObjectType::slUnary_BitwAnd : VObjectType::slBinOp_BitwAnd; break;
        case SV3_1aParser::BITW_OR: object->m_type = isUnary.value() ? VObjectType::slUnary_BitwOr : VObjectType::slBinOp_BitwOr; break;
        case SV3_1aParser::BITW_XOR: object->m_type = isUnary.value() ? VObjectType::slUnary_BitwXor : VObjectType::slBinOp_BitwXor; break;
        case SV3_1aParser::MINUS: object->m_type = isUnary.value() ? VObjectType::slUnary_Minus : VObjectType::slBinOp_Minus; break;
        case SV3_1aParser::PLUS: object->m_type = isUnary.value() ? VObjectType::slUnary_Plus : VObjectType::slBinOp_Plus; break;
        case SV3_1aParser::REDUCTION_NAND: object->m_type = isUnary.value() ? VObjectType::slUnary_ReductNand : VObjectType::slBinOp_ReductNand; break;
        case SV3_1aParser::REDUCTION_XNOR1: object->m_type = isUnary.value() ? VObjectType::slUnary_ReductXnor1 : VObjectType::slBinOp_ReductXnor1; break;
        case SV3_1aParser::REDUCTION_XNOR2: object->m_type = isUnary.value() ? VObjectType::slUnary_ReductXnor2 : VObjectType::slBinOp_ReductXnor2; break;
        case SV3_1aParser::STAR: object->m_type = VObjectType::slBinOp_Mult; break;
        default: break;
      }
      // clang-format on
    }

    applyColumnOffsets(nodeId);
  }
}

void SV3_1aParseTreeListener::visitErrorNode(antlr4::tree::ErrorNode *node) {
  if (node->getText().find("<missing ") != 0) {
    if (NodeId nodeId = addVObject(node, VObjectType::slUnparsable_Text)) {
      applyColumnOffsets(nodeId);
    }
  }
}
}  // namespace SURELOG
