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
 * File:   ParseUtils.cpp
 * Author: alain
 *
 * Created on March 16, 2017, 10:23 PM
 */
#include "Utils/ParseUtils.h"

#include <vector>

#include "antlr4-runtime.h"

namespace SURELOG {

std::pair<int, int> ParseUtils::getLineColumn(
    antlr4::tree::TerminalNode* node) {
  antlr4::Token* token = node->getSymbol();
  int lineNb = token->getLine();
  int columnNb = token->getCharPositionInLine();
  return std::make_pair(lineNb, columnNb);
}

std::pair<int, int> ParseUtils::getEndLineColumn(
    antlr4::tree::TerminalNode* node) {
  antlr4::Token* token = node->getSymbol();
  int lineNb = token->getLine();
  int columnNb = token->getCharPositionInLine() + token->getStopIndex() -
                 token->getStartIndex();
  return std::make_pair(lineNb, columnNb);
}

std::pair<int, int> ParseUtils::getLineColumn(
    antlr4::CommonTokenStream* stream, antlr4::ParserRuleContext* context) {
  const antlr4::misc::Interval sourceInterval =
      ((antlr4::ParserRuleContext*)context)->getSourceInterval();
  if (sourceInterval.a == -1) return std::make_pair(0, 0);
  antlr4::Token* firstToken = stream->get(sourceInterval.a);
  int lineNb = firstToken->getLine();
  int columnNb = firstToken->getCharPositionInLine() + 1;
  return std::make_pair(lineNb, columnNb);
}

std::pair<int, int> ParseUtils::getEndLineColumn(
    antlr4::CommonTokenStream* stream, antlr4::ParserRuleContext* context) {
  const antlr4::misc::Interval sourceInterval =
      ((antlr4::ParserRuleContext*)context)->getSourceInterval();
  if (sourceInterval.b == -1) return std::make_pair(0, 0);
  antlr4::Token* firstToken = stream->get(sourceInterval.b);
  int lineNb = firstToken->getLine();
  int columnNb = firstToken->getCharPositionInLine() +
                 firstToken->getStopIndex() - firstToken->getStartIndex() + 1 +
                 1;
  return std::make_pair(lineNb, columnNb);
}

std::vector<antlr4::tree::ParseTree*> ParseUtils::getTopTokenList(
    antlr4::tree::ParseTree* tree) {
  std::vector<antlr4::tree::ParseTree*> tokens;
  for (unsigned int i = 0; i < tree->children.size(); i++) {
    // Get the i-th child node of `parent`.
    antlr4::tree::ParseTree* child = tree->children[i];
    tokens.push_back(child);
  }
  return tokens;
}

void ParseUtils::tokenizeAtComma(
    std::vector<std::string>& actualArgs,
    const std::vector<antlr4::tree::ParseTree*>& tokens) {
  bool notEmpty = false;
  std::vector<std::string> tmpArgs;
  unsigned int topIndex = 0;
  for (std::vector<antlr4::tree::ParseTree*>::const_iterator itr =
           tokens.begin();
       itr != tokens.end(); itr++) {
    std::string s = (*itr)->getText();
    if (s == ",") {
      tmpArgs.push_back(",");
      topIndex++;
    } else if (s == " ") {
      if (topIndex > 0) {
        if (tmpArgs[topIndex - 1] != ",") tmpArgs[topIndex - 1] += " ";
      }
    } else {
      if ((topIndex == 0) || (tmpArgs[topIndex - 1] == ",")) {
        tmpArgs.push_back(s);
        topIndex++;
      } else
        tmpArgs[topIndex - 1] += s;
    }
  }

  for (unsigned int j = 0; j < tmpArgs.size(); j++) {
    std::string s = tmpArgs[j];
    if (s != ",") {
      for (unsigned int i = 0; i < s.size(); i++) {
        if (s[i] != ' ') {
          notEmpty = true;
          break;
        }
      }
    }
    bool lastToken = (j == (tmpArgs.size() - 1));
    if ((s != ",") && notEmpty) {
      actualArgs.push_back(s);
    } else if ((s == ",") && (!notEmpty)) {
      actualArgs.push_back("");
      notEmpty = false;
      if (lastToken) actualArgs.push_back("");
    } else if (lastToken) {
      actualArgs.push_back("");
    } else if (s == ",") {
      notEmpty = false;
    }
  }
}

/**
 * Retrieves all Tokens from the {@code tree} in an in-order sequence.
 *
 * @param tree
 *         the parse tee to get all tokens from.
 *
 * @return all Tokens from the {@code tree} in an in-order sequence.
 */

std::vector<antlr4::Token*> ParseUtils::getFlatTokenList(
    antlr4::tree::ParseTree* tree) {
  std::vector<antlr4::Token*> tokens;
  inOrderTraversal(tokens, tree);
  return tokens;
}

/**
 * Makes an in-order traversal over {@code parent} (recursively) collecting
 * all Tokens of the terminal nodes it encounters.
 *
 * @param tokens
 *         the list of tokens.
 * @param parent
 *         the current parent node to inspect for terminal nodes.
 */

void ParseUtils::inOrderTraversal(std::vector<antlr4::Token*>& tokens,
                                  antlr4::tree::ParseTree* parent) {
  // Iterate over all child nodes of `parent`.
  for (unsigned int i = 0; i < parent->children.size(); i++) {
    // Get the i-th child node of `parent`.
    antlr4::tree::ParseTree* child = parent->children[i];
    antlr4::tree::TerminalNode* node =
        dynamic_cast<antlr4::tree::TerminalNode*>(child);
    if (node) {
      // We found a leaf/terminal, add its Token to our list.
      tokens.push_back(node->getSymbol());
    } else {
      // No leaf/terminal node, recursively call this method.
      inOrderTraversal(tokens, child);
    }
  }
}
}  // namespace SURELOG
