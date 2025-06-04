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

#include <Surelog/Common/Containers.h>

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

namespace antlr4 {
class CommonTokenStream;
class Token;
class ParserRuleContext;
namespace tree {
class ParseTree;
class TerminalNode;
}  // namespace tree
}  // namespace antlr4

namespace SURELOG::ParseUtils {
LineColumn getLineColumn(const antlr4::CommonTokenStream* stream,
                         antlr4::tree::ParseTree* tree);
LineColumn getEndLineColumn(const antlr4::CommonTokenStream* stream,
                            antlr4::tree::ParseTree* tree);

LineColumn getLineColumn(antlr4::Token* token);
LineColumn getEndLineColumn(antlr4::Token* token);

LineColumn getLineColumn(antlr4::tree::TerminalNode* node);
LineColumn getEndLineColumn(antlr4::tree::TerminalNode* node);

const std::vector<antlr4::tree::ParseTree*>& getTopTokenList(
    const antlr4::tree::ParseTree* tree);
void tokenizeAtComma(std::vector<std::string>& actualArgs,
                     const std::vector<antlr4::tree::ParseTree*>& tokens);

std::vector<antlr4::Token*> getFlatTokenList(antlr4::tree::ParseTree* tree);

void inOrderTraversal(std::vector<antlr4::Token*>& tokens,
                      const antlr4::tree::ParseTree* parent);
}  // namespace SURELOG::ParseUtils

#endif /* SURELOG_PARSEUTILS_H */
