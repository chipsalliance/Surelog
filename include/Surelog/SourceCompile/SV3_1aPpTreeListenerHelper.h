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
 * File:   SV3_1aPpTreeListenerHelper.h
 * Author: alain
 *
 * Created on December 4, 2019, 8:17 PM
 */

#ifndef SURELOG_SV3_1APPTREELISTENERHELPER_H
#define SURELOG_SV3_1APPTREELISTENERHELPER_H
#pragma once

#include <Surelog/Common/PathId.h>
#include <Surelog/Common/SymbolId.h>
#include <Surelog/ErrorReporting/ErrorDefinition.h>
#include <Surelog/ErrorReporting/Location.h>
#include <Surelog/SourceCompile/CommonListenerHelper.h>
#include <Surelog/SourceCompile/PreprocessFile.h>

#include <cstdint>
#include <set>
#include <string_view>
#include <tuple>
#include <vector>

namespace SURELOG {
class SV3_1aPpTreeListenerHelper : public CommonListenerHelper {
 public:
  ~SV3_1aPpTreeListenerHelper() override = default;

 protected:
  // Helper function if-else
  void setCurrentBranchActivity(uint32_t currentLine);
  // Helper function if-else
  bool isPreviousBranchActive() const;
  // Helper function to log errors
  void logError(ErrorDefinition::ErrorType error,
                antlr4::ParserRuleContext* ctx, std::string_view object,
                bool printColumn = false);
  void logError(ErrorDefinition::ErrorType, Location& loc,
                bool showDuplicates = false);
  void logError(ErrorDefinition::ErrorType, Location& loc, Location& extraLoc,
                bool showDuplicates = false);
  void checkMultiplyDefinedMacro(std::string_view macroName,
                                 antlr4::ParserRuleContext* ctx);
  void forwardToParser(antlr4::ParserRuleContext* ctx);
  void init();
  void addLineFiller(antlr4::ParserRuleContext* ctx);

  SymbolId registerSymbol(std::string_view symbol) final;

  std::tuple<PathId, uint32_t, uint16_t, uint32_t, uint16_t> getPPFileLine(
      antlr4::tree::ParseTree* tree, antlr4::Token* token) const final;
  std::tuple<PathId, uint32_t, uint16_t, uint32_t, uint16_t> getFileLine(
      antlr4::tree::ParseTree* tree, antlr4::Token* token) const final {
    return getPPFileLine(tree, token);
  }

 protected:
  SV3_1aPpTreeListenerHelper(Session* session, PreprocessFile* pp,
                             PreprocessFile::SpecialInstructions& instructions,
                             antlr4::CommonTokenStream* tokens);

 protected:
  PreprocessFile* m_pp = nullptr;
  bool m_inActiveBranch = false;
  bool m_inMacroDefinitionParsing = false;
  bool m_inProtectedRegion = false;
  bool m_filterProtectedRegions = false;
  std::set<std::string_view> m_reservedMacroNamesSet;
  antlr4::tree::ParseTree* m_appendPausedContext = nullptr;
  PreprocessFile::SpecialInstructions m_instructions;
};

}  // namespace SURELOG

#endif /* SURELOG_SV3_1APPTREELISTENERHELPER_H */
