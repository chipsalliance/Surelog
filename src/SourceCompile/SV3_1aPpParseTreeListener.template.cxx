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
 * File:   SV3_1aPpParseTreeListener.cpp
 * Author: hs
 *
 * Created on January 31, 2023, 12:00 PM
 */

#include <Surelog/Design/FileContent.h>
#include <Surelog/SourceCompile/CompileSourceFile.h>
#include <Surelog/SourceCompile/PreprocessFile.h>
#include <Surelog/SourceCompile/SV3_1aPpParseTreeListener.h>
#include <Surelog/Utils/ParseUtils.h>
#include <Surelog/Utils/StringUtils.h>
#include <parser/SV3_1aPpParser.h>

namespace SURELOG {
SV3_1aPpParseTreeListener::SV3_1aPpParseTreeListener(
    PreprocessFile *pp, antlr4::CommonTokenStream *tokens,
    PreprocessFile::SpecialInstructions &instructions)
    : SV3_1aPpTreeListenerHelper(pp, instructions, tokens) {
  if (m_pp->getFileContent() == nullptr) {
    m_fileContent = new FileContent(
        m_pp->getFileId(0), m_pp->getLibrary(),
        m_pp->getCompileSourceFile()->getSymbolTable(),
        m_pp->getCompileSourceFile()->getErrorContainer(), nullptr, BadPathId);
    m_pp->setFileContent(m_fileContent);
  } else {
    m_fileContent = m_pp->getFileContent();
  }
}

bool SV3_1aPpParseTreeListener::isOnCallStack(int32_t ruleIndex) const {
  return std::find(m_callstack.crbegin(), m_callstack.crend(), ruleIndex) !=
         m_callstack.crend();
}

bool SV3_1aPpParseTreeListener::isAnyOnCallStack(
  const std::unordered_set<int32_t> &ruleIndicies) const {
  for (callstack_t::const_reverse_iterator it = m_callstack.crbegin(),
                                           end = m_callstack.crend();
       it != end; ++it) {
    if (ruleIndicies.find(*it) != ruleIndicies.end()) {
      return true;
    }
  }
  return false;
}

void SV3_1aPpParseTreeListener::enterEscaped_identifier(
    SV3_1aPpParser::Escaped_identifierContext *ctx) {
  if (isOnCallStack(SV3_1aPpParser::RuleMacro_definition)) return;

  const std::string text = ctx->getText();

  std::string sequence = EscapeSequence;
  sequence.append(++text.cbegin(), text.cend());
  sequence.append(EscapeSequence);

  m_pp->append(sequence);
}

void SV3_1aPpParseTreeListener::exitIfdef_directive(
    SV3_1aPpParser::Ifdef_directiveContext *ctx) {
  const size_t index =
      (RawNodeId)addVObject(ctx, VObjectType::slIfdef_directive);
  m_pp->append(StrCat("@~#", index, std::string(m_pendingCRs, '\n')));
  m_visitedRules.emplace(ctx);
  m_pendingCRs = 0;
}

void SV3_1aPpParseTreeListener::exitIfndef_directive(
    SV3_1aPpParser::Ifndef_directiveContext *ctx) {
  const size_t index =
      (RawNodeId)addVObject(ctx, VObjectType::slIfndef_directive);
  m_pp->append(StrCat("@~#", index, std::string(m_pendingCRs, '\n')));
  m_visitedRules.emplace(ctx);
  m_pendingCRs = 0;
}

void SV3_1aPpParseTreeListener::exitUndef_directive(
    SV3_1aPpParser::Undef_directiveContext *ctx) {
  const size_t index =
      (RawNodeId)addVObject(ctx, VObjectType::slUndef_directive);
  m_pp->append(StrCat("@~#", index, std::string(m_pendingCRs, '\n')));
  m_visitedRules.emplace(ctx);
  m_pendingCRs = 0;
}

void SV3_1aPpParseTreeListener::exitElsif_directive(
    SV3_1aPpParser::Elsif_directiveContext *ctx) {
  const size_t index =
      (RawNodeId)addVObject(ctx, VObjectType::slElsif_directive);
  m_pp->append(StrCat("@~#", index, std::string(m_pendingCRs, '\n')));
  m_visitedRules.emplace(ctx);
  m_pendingCRs = 0;
}

void SV3_1aPpParseTreeListener::exitElse_directive(
    SV3_1aPpParser::Else_directiveContext *ctx) {
  const size_t index =
      (RawNodeId)addVObject(ctx, VObjectType::slElse_directive);
  m_pp->append(StrCat("@~#", index, std::string(m_pendingCRs, '\n')));
  m_visitedRules.emplace(ctx);
  m_pendingCRs = 0;
}

void SV3_1aPpParseTreeListener::exitElseif_directive(
    SV3_1aPpParser::Elseif_directiveContext *ctx) {
  const size_t index =
      (RawNodeId)addVObject(ctx, VObjectType::slElseif_directive);
  m_pp->append(StrCat("@~#", index, std::string(m_pendingCRs, '\n')));
  m_visitedRules.emplace(ctx);
  m_pendingCRs = 0;
}

void SV3_1aPpParseTreeListener::exitEndif_directive(
    SV3_1aPpParser::Endif_directiveContext *ctx) {
  const size_t index =
      (RawNodeId)addVObject(ctx, VObjectType::slEndif_directive);
  m_pp->append(StrCat("@~#", index, std::string(m_pendingCRs, '\n')));
  m_visitedRules.emplace(ctx);
  m_pendingCRs = 0;
}

void SV3_1aPpParseTreeListener::exitInclude_directive(
    SV3_1aPpParser::Include_directiveContext *ctx) {
  if (isOnCallStack(SV3_1aPpParser::RuleMacro_definition)) return;

  const int32_t index =
      (RawNodeId)addVObject(ctx, VObjectType::slInclude_directive);
  m_pp->append(StrCat("@~#", index, std::string(m_pendingCRs, '\n')));
  m_visitedRules.insert(ctx);
  m_pendingCRs = 0;
}

void SV3_1aPpParseTreeListener::exitLine_directive(
  SV3_1aPpParser::Line_directiveContext *ctx) {
  const int32_t index =
      (RawNodeId)addVObject(ctx, VObjectType::slLine_directive);
  m_pp->append(StrCat("@~#", index, std::string(m_pendingCRs, '\n')));
  m_visitedRules.insert(ctx);
  m_pendingCRs = 0;
}

void SV3_1aPpParseTreeListener::exitSv_file_directive(
  SV3_1aPpParser::Sv_file_directiveContext *ctx) {
  const int32_t index =
      (RawNodeId)addVObject(ctx, VObjectType::slSv_file_directive);
  m_pp->append(StrCat("@~#", index, std::string(m_pendingCRs, '\n')));
  m_visitedRules.insert(ctx);
  m_pendingCRs = 0;
}

void SV3_1aPpParseTreeListener::exitSv_line_directive(
  SV3_1aPpParser::Sv_line_directiveContext *ctx) {
  const int32_t index =
      (RawNodeId)addVObject(ctx, VObjectType::slSv_line_directive);
  m_pp->append(StrCat("@~#", index, std::string(m_pendingCRs, '\n')));
  m_visitedRules.insert(ctx);
  m_pendingCRs = 0;
}

void SV3_1aPpParseTreeListener::exitMacroInstanceWithArgs(
    SV3_1aPpParser::MacroInstanceWithArgsContext *ctx) {
  const size_t index =
      (RawNodeId)addVObject(ctx, VObjectType::slMacro_instance);
  const std::string text = ctx->getText();
  m_pendingCRs += std::count(text.begin(), text.end(), '\n');
  // if (ctx->CR() != nullptr) --m_pendingCRs;
  m_pp->append(StrCat("@~#", index, std::string(m_pendingCRs, '\n')));
  m_visitedRules.emplace(ctx);
  m_pendingCRs = 0;
}

void SV3_1aPpParseTreeListener::exitMacroInstanceNoArgs(
    SV3_1aPpParser::MacroInstanceNoArgsContext *ctx) {
  const int32_t index =
      (RawNodeId)addVObject(ctx, VObjectType::slMacro_instance);
  const std::string text = ctx->getText();
  m_pendingCRs += std::count(text.begin(), text.end(), '\n');
  // if (ctx->CR() != nullptr) --m_pendingCRs;
  m_pp->append(StrCat("@~#", index, std::string(m_pendingCRs, '\n')));
  m_visitedRules.emplace(ctx);
  m_pendingCRs = 0;
}

void SV3_1aPpParseTreeListener::exitMacro_definition(
    SV3_1aPpParser::Macro_definitionContext *ctx) {
  const int32_t index =
      (RawNodeId)addVObject(ctx, VObjectType::slMacro_definition);
  const std::string text = ctx->getText();
  m_pendingCRs += std::count(text.begin(), text.end(), '\n');
  m_pp->append(StrCat("@~#", index, std::string(m_pendingCRs, '\n')));
  m_visitedRules.emplace(ctx);
  m_pendingCRs = 0;
}

void SV3_1aPpParseTreeListener::exitSimple_macro_definition_body(
    SV3_1aPpParser::Simple_macro_definition_bodyContext *ctx) {
  addVObject(ctx, ctx->getText(), VObjectType::slSimple_macro_definition_body);
}

void SV3_1aPpParseTreeListener::exitEscaped_macro_definition_body(
    SV3_1aPpParser::Escaped_macro_definition_bodyContext *ctx) {
  addVObject(ctx, ctx->getText(), VObjectType::slEscaped_macro_definition_body);
}

void SV3_1aPpParseTreeListener::exitMacro_arg(
    SV3_1aPpParser::Macro_argContext *ctx) {
  addVObject(ctx, ctx->getText(), VObjectType::slMacro_arg);
}

void SV3_1aPpParseTreeListener::enterEveryRule(antlr4::ParserRuleContext *ctx) {
  m_callstack.emplace_back(ctx->getRuleIndex());
}

void SV3_1aPpParseTreeListener::exitEveryRule(antlr4::ParserRuleContext *ctx) {
  if (!m_callstack.empty() && (m_callstack.back() == ctx->getRuleIndex())) {
    m_callstack.pop_back();
  }

  if (!m_visitedRules.insert(ctx).second) return;

  if (isAnyOnCallStack({
          SV3_1aPpParser::RuleEscaped_macro_definition_body,
          SV3_1aPpParser::RuleSimple_macro_definition_body,
          SV3_1aPpParser::RuleMacro_arg
      })) {
    return;
  }

  // clang-format off
  switch (ctx->getRuleIndex()) {
<RULE_CASE_STATEMENTS>
    default: break;
   }
  // clang-format on
}

void SV3_1aPpParseTreeListener::visitTerminal(
    antlr4::tree::TerminalNode *node) {
  const antlr4::Token *const token = node->getSymbol();
  if (token->getType() == antlr4::Token::EOF) return;
  if (!m_visitedTokens.insert(token).second) return;

  if (isAnyOnCallStack({
          SV3_1aPpParser::RuleEscaped_macro_definition_body,
          SV3_1aPpParser::RuleSimple_macro_definition_body,
          SV3_1aPpParser::RuleMacro_arg
      })) {
    return;
  }

  if (!isAnyOnCallStack({
    SV3_1aPpParser::RuleMacro_instance,
    SV3_1aPpParser::RuleMacro_definition,
    SV3_1aPpParser::RuleInclude_directive,
    SV3_1aPpParser::RuleLine_directive,
    SV3_1aPpParser::RuleSv_file_directive,
    SV3_1aPpParser::RuleSv_line_directive,
    SV3_1aPpParser::RuleIfdef_directive,
    SV3_1aPpParser::RuleIfndef_directive,
    SV3_1aPpParser::RuleUndef_directive,
    SV3_1aPpParser::RuleElsif_directive,
    SV3_1aPpParser::RuleElse_directive,
    SV3_1aPpParser::RuleElseif_directive,
    SV3_1aPpParser::RuleEndif_directive})) {
    if (token->getType() != SV3_1aPpParser::Escaped_identifier) {
      m_pp->append(node->getText());
    }
  } else if ((token->getType() == SV3_1aPpParser::CR) ||
             (token->getType() == SV3_1aPpParser::ESCAPED_CR)) {
    ++m_pendingCRs;
  }

  // clang-format off
  switch (token->getType()) {
<VISIT_CASE_STATEMENTS>
    default: break;
  }
  // clang-format on
}
}  // namespace SURELOG
