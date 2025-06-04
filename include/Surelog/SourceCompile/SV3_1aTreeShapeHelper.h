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
 * File:   SV3_1aTreeShapeHelper.h
 * Author: alain
 *
 * Created on June 25, 2017, 2:51 PM
 */

#ifndef SURELOG_SV3_1ATREESHAPEHELPER_H
#define SURELOG_SV3_1ATREESHAPEHELPER_H
#pragma once

#include <Surelog/Common/NodeId.h>
#include <Surelog/Common/PathId.h>
#include <Surelog/Common/SymbolId.h>
#include <Surelog/Design/DesignElement.h>
#include <Surelog/ErrorReporting/ErrorDefinition.h>
#include <Surelog/ErrorReporting/Location.h>
#include <Surelog/SourceCompile/CommonListenerHelper.h>
#include <Surelog/SourceCompile/IncludeFileInfo.h>
#include <Surelog/SourceCompile/VObjectTypes.h>
#include <parser/SV3_1aParser.h>

#include <cstdint>
#include <stack>
#include <string_view>
#include <tuple>
#include <utility>

namespace antlr4 {
class CommonTokenStream;
}

namespace SURELOG {

#define SV_MAX_IDENTIFIER_SIZE 1024
#define SV_MAX_STRING_SIZE (4 * 1024 * 1024)

class ParseFile;
class ParseLibraryDef;
class Session;

class SV3_1aTreeShapeHelper : public CommonListenerHelper {
 public:
  ~SV3_1aTreeShapeHelper() override = default;

 protected:
  void logError(ErrorDefinition::ErrorType error,
                antlr4::ParserRuleContext* ctx, std::string_view object,
                bool printColumn = false);

  void logError(ErrorDefinition::ErrorType, Location& loc,
                bool showDuplicates = false);

  void logError(ErrorDefinition::ErrorType, Location& loc, Location& extraLoc,
                bool showDuplicates = false);

  NodeId generateDesignElemId();

  NodeId generateNodeId();

  SymbolId registerSymbol(std::string_view symbol) override;

  void addNestedDesignElement(antlr4::ParserRuleContext* ctx,
                              std::string_view name,
                              DesignElement::ElemType elemtype,
                              VObjectType objtype);

  void addDesignElement(antlr4::ParserRuleContext* ctx, std::string_view name,
                        DesignElement::ElemType elemtype, VObjectType objtype);

  std::pair<double, TimeInfo::Unit> getTimeValue(
      SV3_1aParser::Time_literalContext* ctx);

  std::tuple<PathId, uint32_t, uint16_t, uint32_t, uint16_t> getPPFileLine(
      antlr4::tree::ParseTree* tree, antlr4::Token* token) const override;
  std::tuple<PathId, uint32_t, uint16_t, uint32_t, uint16_t> getFileLine(
      antlr4::tree::ParseTree* tree, antlr4::Token* token) const final;

 protected:
  SV3_1aTreeShapeHelper(Session* session, ParseFile* pf,
                        antlr4::CommonTokenStream* tokens, uint32_t lineOffset);

  SV3_1aTreeShapeHelper(Session* session, ParseLibraryDef* pf,
                        antlr4::CommonTokenStream* tokens);

 protected:
  ParseFile* m_pf = nullptr;
  DesignElement* m_currentElement = nullptr;
  std::stack<DesignElement*> m_nestedElements;
  uint32_t m_lineOffset = 0;
  bool m_ppOutputFileLocation = false;
  std::stack<IncludeFileInfo> m_includeFileInfo;
};

};  // namespace SURELOG

#endif /* SURELOG_SV3_1ATREESHAPEHELPER_H */
