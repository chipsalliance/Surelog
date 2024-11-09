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
 * File:   ParseUtils.h
 * Author: alain
 *
 * Created on March 16, 2017, 10:23 PM
 */

#ifndef SURELOG_PARSEUTILS_H
#define SURELOG_PARSEUTILS_H
#pragma once

#include <utility>
#include <vector>
#include <string>
#include <ParserRuleContext.h>

namespace SURELOG {
namespace ParseUtils {
using ParseTree = antlr4::tree::ParseTree;
using LineColumn = std::pair<uint32_t, uint16_t>;

LineColumn getLineColumn(antlr4::CommonTokenStream* stream,
                         antlr4::ParserRuleContext* context);
LineColumn getEndLineColumn(antlr4::CommonTokenStream* stream,
                            antlr4::ParserRuleContext* context);

LineColumn getLineColumn(antlr4::Token* token);
LineColumn getEndLineColumn(antlr4::Token* token);

LineColumn getLineColumn(antlr4::tree::TerminalNode* node);
LineColumn getEndLineColumn(antlr4::tree::TerminalNode* node);

const std::vector<ParseTree*>& getTopTokenList(ParseTree* tree);
void tokenizeAtComma(std::vector<std::string>& actualArgs,
                     const std::vector<ParseTree*>& tokens);

std::vector<antlr4::Token*> getFlatTokenList(ParseTree* tree);

void inOrderTraversal(std::vector<antlr4::Token*>& tokens, ParseTree* parent);
}  // namespace ParseUtils

}  // namespace SURELOG

#endif /* SURELOG_PARSEUTILS_H */
