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
 * File:   SV3_1aPpParseTreeListener.h
 * Author: hs
 *
 * Created on January 31, 2023, 12:00 PM
 */

#ifndef SURELOG_SV3_1APPPARSETREELISTENER_H
#define SURELOG_SV3_1APPPARSETREELISTENER_H
#pragma once

#include <Surelog/SourceCompile/SV3_1aPpTreeListenerHelper.h>
#include <parser/SV3_1aPpParserBaseListener.h>

#include <regex>

namespace SURELOG {
class PreprocessFile;
class SV3_1aPpParseTreeListener final : public SV3_1aPpParserBaseListener,
                                        public SV3_1aPpTreeListenerHelper {
 public:
  SV3_1aPpParseTreeListener(PreprocessFile* pp,
                            antlr4::CommonTokenStream* tokens,
                            PreprocessFile::SpecialInstructions& instructions);
  ~SV3_1aPpParseTreeListener() override = default;

  void enterEscaped_identifier(
      SV3_1aPpParser::Escaped_identifierContext* ctx) final;
  void exitIfdef_directive(SV3_1aPpParser::Ifdef_directiveContext* ctx) final;
  void exitIfndef_directive(
      SV3_1aPpParser::Ifndef_directiveContext* ctx) final;
  void exitUndef_directive(SV3_1aPpParser::Undef_directiveContext* ctx) final;
  void exitElsif_directive(SV3_1aPpParser::Elsif_directiveContext* ctx) final;
  void exitElse_directive(SV3_1aPpParser::Else_directiveContext* ctx) final;
  void exitElseif_directive(SV3_1aPpParser::Elseif_directiveContext* ctx) final;
  void exitEndif_directive(SV3_1aPpParser::Endif_directiveContext* ctx) final;
  void exitInclude_directive(
      SV3_1aPpParser::Include_directiveContext* ctx) final;
  void exitLine_directive(SV3_1aPpParser::Line_directiveContext* ctx) final;
  void exitSv_file_directive(
      SV3_1aPpParser::Sv_file_directiveContext* ctx) final;
  void exitSv_line_directive(
      SV3_1aPpParser::Sv_line_directiveContext* ctx) final;

  void exitMacroInstanceWithArgs(
      SV3_1aPpParser::MacroInstanceWithArgsContext* ctx) final;
  void exitMacroInstanceNoArgs(
      SV3_1aPpParser::MacroInstanceNoArgsContext* ctx) final;
  void exitMacro_definition(SV3_1aPpParser::Macro_definitionContext* ctx) final;
  void exitSimple_macro_definition_body(
      SV3_1aPpParser::Simple_macro_definition_bodyContext* ctx) final;
  void exitEscaped_macro_definition_body(
      SV3_1aPpParser::Escaped_macro_definition_bodyContext* ctx) final;
  void exitMacro_arg(SV3_1aPpParser::Macro_argContext* ctx) final;

  void enterEveryRule(antlr4::ParserRuleContext* ctx) final;
  void exitEveryRule(antlr4::ParserRuleContext* ctx) final;
  void visitTerminal(antlr4::tree::TerminalNode* node) final;

 private:
  using SV3_1aPpTreeListenerHelper::addVObject;

  bool isOnCallStack(int32_t ruleIndex) const;
  bool isAnyOnCallStack(const std::unordered_set<int32_t>& ruleIndicies) const;

 private:
  typedef std::vector<size_t> callstack_t;

  std::set<const antlr4::ParserRuleContext*> m_visitedRules;
  std::set<const antlr4::Token*> m_visitedTokens;
  callstack_t m_callstack;
  size_t m_pendingCRs = 0;
};
}  // namespace SURELOG

#endif  // SURELOG_SV3_1APPPARSETREELISTENER_H
