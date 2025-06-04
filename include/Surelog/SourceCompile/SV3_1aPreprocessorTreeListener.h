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
 * File:   SV3_1aPreprocessorTreeListener.h
 * Author: hs
 *
 * Created on January 31, 2023, 12:00 PM
 */

#ifndef SURELOG_SV3_1APREPROCESSORTREELISTENER_H
#define SURELOG_SV3_1APREPROCESSORTREELISTENER_H
#pragma once

#include <Surelog/SourceCompile/MacroInfo.h>
#include <Surelog/SourceCompile/SV3_1aPpTreeListenerHelper.h>
#include <parser/SV3_1aPpParserBaseListener.h>

namespace SURELOG {
class PreprocessFile;
class Session;
class SV3_1aPreprocessorTreeListener final : public SV3_1aPpParserBaseListener,
                                             public SV3_1aPpTreeListenerHelper {
 public:
  SV3_1aPreprocessorTreeListener(
      Session* session, PreprocessFile* pp, antlr4::CommonTokenStream* tokens,
      PreprocessFile::SpecialInstructions& instructions);
  ~SV3_1aPreprocessorTreeListener() final = default;

  void enterString(SV3_1aPpParser::StringContext* ctx) final;
  void enterEscaped_identifier(
      SV3_1aPpParser::Escaped_identifierContext* ctx) final;

  void enterIfdef_directive(SV3_1aPpParser::Ifdef_directiveContext* ctx) final;
  void exitIfdef_directive(SV3_1aPpParser::Ifdef_directiveContext* ctx) final;

  void enterIfndef_directive(
      SV3_1aPpParser::Ifndef_directiveContext* ctx) final;
  void exitIfndef_directive(SV3_1aPpParser::Ifndef_directiveContext* ctx) final;

  void enterUndef_directive(SV3_1aPpParser::Undef_directiveContext* ctx) final;
  void exitUndef_directive(SV3_1aPpParser::Undef_directiveContext* ctx) final;

  void enterElsif_directive(SV3_1aPpParser::Elsif_directiveContext* ctx) final;
  void exitElsif_directive(SV3_1aPpParser::Elsif_directiveContext* ctx) final;

  void enterElse_directive(SV3_1aPpParser::Else_directiveContext* ctx) final;
  void exitElse_directive(SV3_1aPpParser::Else_directiveContext* ctx) final;

  void enterEndif_directive(SV3_1aPpParser::Endif_directiveContext* ctx) final;
  void exitEndif_directive(SV3_1aPpParser::Endif_directiveContext* ctx) final;

  void enterInclude_directive(
      SV3_1aPpParser::Include_directiveContext* ctx) final;
  void exitInclude_directive(
      SV3_1aPpParser::Include_directiveContext* ctx) final;

  void enterLine_directive(SV3_1aPpParser::Line_directiveContext* ctx) final;
  void exitLine_directive(SV3_1aPpParser::Line_directiveContext* ctx) final;

  void enterSv_file_directive(
      SV3_1aPpParser::Sv_file_directiveContext* ctx) final;
  void exitSv_file_directive(
      SV3_1aPpParser::Sv_file_directiveContext* ctx) final;

  void enterSv_line_directive(
      SV3_1aPpParser::Sv_line_directiveContext* ctx) final;
  void exitSv_line_directive(
      SV3_1aPpParser::Sv_line_directiveContext* ctx) final;

  void enterMacroInstanceWithArgs(
      SV3_1aPpParser::MacroInstanceWithArgsContext* ctx) final;
  void exitMacroInstanceWithArgs(
      SV3_1aPpParser::MacroInstanceWithArgsContext* ctx) final;

  void enterMacroInstanceNoArgs(
      SV3_1aPpParser::MacroInstanceNoArgsContext* ctx) final;
  void exitMacroInstanceNoArgs(
      SV3_1aPpParser::MacroInstanceNoArgsContext* ctx) final;

  void enterMacro_definition(
      SV3_1aPpParser::Macro_definitionContext* ctx) final;
  void exitMacro_definition(SV3_1aPpParser::Macro_definitionContext* ctx) final;

  void enterUndefineall_directive(
      SV3_1aPpParser::Undefineall_directiveContext* ctx) final;
  void exitUndefineall_directive(
      SV3_1aPpParser::Undefineall_directiveContext* ctx) final;

  void enterPragma_directive(
      SV3_1aPpParser::Pragma_directiveContext* ctx) final;
  void exitPragma_directive(SV3_1aPpParser::Pragma_directiveContext* ctx) final;

  void enterComment(SV3_1aPpParser::CommentContext* ctx) final;
  void exitComment(SV3_1aPpParser::CommentContext* ctx) final;

  void enterEveryRule(antlr4::ParserRuleContext* ctx) final;
  void exitEveryRule(antlr4::ParserRuleContext* ctx) final;
  void visitTerminal(antlr4::tree::TerminalNode* node) final;

 private:
  using SV3_1aPpTreeListenerHelper::addVObject;
  NodeId addVObject(antlr4::tree::TerminalNode* node, VObjectType objectType);
  void adjustMacroDefinitionLocation(antlr4::tree::ParseTree* tree,
                                     NodeId nodeId);

  void appendPreprocBegin();
  void appendPreprocEnd();

 private:
  bool m_passThrough = false;
};
}  // namespace SURELOG

#endif  // SURELOG_SV3_1APREPROCESSORTREELISTENER_H
