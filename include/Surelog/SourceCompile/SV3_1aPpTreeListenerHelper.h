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

#include <Surelog/Common/SymbolId.h>
#include <Surelog/ErrorReporting/ErrorDefinition.h>
#include <Surelog/ErrorReporting/Location.h>
#include <Surelog/SourceCompile/CommonListenerHelper.h>
#include <Surelog/SourceCompile/PreprocessFile.h>

#include <set>
#include <vector>

namespace SURELOG {

class SymbolTable;

class SV3_1aPpTreeListenerHelper : public CommonListenerHelper {
 protected:
  PreprocessFile* m_pp;
  bool m_inActiveBranch;
  bool m_inMacroDefinitionParsing;
  bool m_inProtectedRegion;
  bool m_filterProtectedRegions;
  std::vector<std::string> m_reservedMacroNames;
  std::set<std::string> m_reservedMacroNamesSet;
  antlr4::ParserRuleContext* m_append_paused_context;
  PreprocessFile::SpecialInstructions m_instructions;

 public:
  SV3_1aPpTreeListenerHelper(PreprocessFile* pp,
                             PreprocessFile::SpecialInstructions& instructions,
                             antlr4::CommonTokenStream* tokens)
      : CommonListenerHelper(nullptr, tokens),
        m_pp(pp),
        m_inActiveBranch(true),
        m_inMacroDefinitionParsing(false),
        m_inProtectedRegion(false),
        m_filterProtectedRegions(false),
        m_append_paused_context(nullptr),
        m_instructions(instructions) {
    init();
  }

  // Helper function if-else
  void setCurrentBranchActivity(unsigned int currentLine);
  // Helper function if-else
  bool isPreviousBranchActive();
  // Helper function to log errors
  void logError(ErrorDefinition::ErrorType error,
                antlr4::ParserRuleContext* ctx, std::string object,
                bool printColumn = false);
  void logError(ErrorDefinition::ErrorType, Location& loc,
                bool showDuplicates = false);
  void logError(ErrorDefinition::ErrorType, Location& loc, Location& extraLoc,
                bool showDuplicates = false);
  void checkMultiplyDefinedMacro(const std::string& macroName,
                                 antlr4::ParserRuleContext* ctx);
  void forwardToParser(antlr4::ParserRuleContext* ctx);
  void init();
  void addLineFiller(antlr4::ParserRuleContext* ctx);

  SymbolTable* getSymbolTable() const;
  SymbolId registerSymbol(const std::string& symbol) final;

  std::tuple<unsigned int, unsigned short, unsigned int, unsigned short>
  getFileLine(antlr4::ParserRuleContext* ctx, SymbolId& fileId) override;

  ~SV3_1aPpTreeListenerHelper() override = default;
};

}  // namespace SURELOG

#endif /* SURELOG_SV3_1APPTREELISTENERHELPER_H */
