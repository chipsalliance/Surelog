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

#ifndef PARSEUTILS_H
#define PARSEUTILS_H
#include "antlr4-runtime.h"
#include "ParserRuleContext.h"

namespace SURELOG {

class ParseUtils final {
public:
  using ParseTree = antlr4::tree::ParseTree;

  static std::pair<int, int> getLineColumn(antlr4::CommonTokenStream* stream,
                                           antlr4::ParserRuleContext* context);

  static std::pair<int, int> getEndLineColumn(antlr4::CommonTokenStream* stream,
                                           antlr4::ParserRuleContext* context);                                        

  static std::pair<int, int> getLineColumn(antlr4::tree::TerminalNode* node);

   static std::pair<int, int> getEndLineColumn(antlr4::tree::TerminalNode* node);

  static std::vector<ParseTree*> getTopTokenList(ParseTree* tree);
  static void tokenizeAtComma(std::vector<std::string>& actualArgs,
                              const std::vector<ParseTree*>& tokens);

  static std::vector<antlr4::Token*> getFlatTokenList(ParseTree* tree);

  static void inOrderTraversal(std::vector<antlr4::Token*>& tokens,
                               ParseTree* parent);

private:
  ParseUtils() = delete;
  ParseUtils(const ParseUtils& orig) = delete;
};

}  // namespace SURELOG

#endif /* PARSEUTILS_H */
