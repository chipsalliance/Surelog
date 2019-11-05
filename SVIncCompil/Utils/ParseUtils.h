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

namespace SURELOG {

class ParseUtils {
 public:
  static std::pair<int, int> getLineColumn(CommonTokenStream* stream,
                                           ParserRuleContext* context);

  static std::pair<int, int> getLineColumn(tree::TerminalNode* node);

  static std::vector<tree::ParseTree*> getTopTokenList(tree::ParseTree* tree);
  static void tokenizeAtComma(std::vector<std::string>& actualArgs,
                              const std::vector<tree::ParseTree*>& tokens);

  static std::vector<Token*> getFlatTokenList(tree::ParseTree* tree);

  static void inOrderTraversal(std::vector<Token*>& tokens,
                               tree::ParseTree* parent);

 private:
  ParseUtils();
  ParseUtils(const ParseUtils& orig);
  virtual ~ParseUtils();

 private:
};

};  // namespace SURELOG

#endif /* PARSEUTILS_H */
