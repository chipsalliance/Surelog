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

#include <Surelog/Utils/ParseUtils.h>
#include <antlr4-runtime.h>

namespace SURELOG {

ParseUtils::LineColumn ParseUtils::getLineColumn(
    antlr4::tree::TerminalNode* node) {
  const antlr4::Token* token = node->getSymbol();
  const size_t lineNb = token->getLine();
  const size_t columnNb = token->getCharPositionInLine();
  return std::make_pair(lineNb, columnNb);
}

ParseUtils::LineColumn ParseUtils::getEndLineColumn(
    antlr4::tree::TerminalNode* node) {
  const antlr4::Token* token = node->getSymbol();
  const size_t lineNb = token->getLine();
  const size_t columnNb = token->getCharPositionInLine() +
                          token->getStopIndex() - token->getStartIndex();
  return std::make_pair(lineNb, columnNb);
}

ParseUtils::LineColumn ParseUtils::getLineColumn(
    antlr4::CommonTokenStream* stream, antlr4::ParserRuleContext* context) {
  const antlr4::misc::Interval sourceInterval = context->getSourceInterval();
  if (sourceInterval.a == -1) return std::make_pair(0, 0);
  antlr4::Token* firstToken = stream->get(sourceInterval.a);
  const size_t lineNb = firstToken->getLine();
  const size_t columnNb = firstToken->getCharPositionInLine() + 1;
  return std::make_pair(lineNb, columnNb);
}

ParseUtils::LineColumn ParseUtils::getEndLineColumn(
    antlr4::CommonTokenStream* stream, antlr4::ParserRuleContext* context) {
  const antlr4::misc::Interval sourceInterval = context->getSourceInterval();
  if (sourceInterval.b == -1) return std::make_pair(0, 0);
  antlr4::Token* firstToken = stream->get(sourceInterval.b);
  size_t lineNb = firstToken->getLine();
  size_t columnNb = firstToken->getCharPositionInLine() +
                    firstToken->getStopIndex() - firstToken->getStartIndex() +
                    1 + 1;
  return std::make_pair(lineNb, columnNb);
}

std::vector<antlr4::tree::ParseTree*> ParseUtils::getTopTokenList(
    antlr4::tree::ParseTree* tree) {
  std::vector<antlr4::tree::ParseTree*> tokens;
  for (antlr4::tree::ParseTree* child : tree->children) {
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
  for (antlr4::tree::ParseTree* token : tokens) {
    const std::string s = token->getText();
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
    const std::string& s = tmpArgs[j];
    if (s != ",") {
      for (const char c : s) {  // TODO: use std:: fun
        if (c != ' ') {
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
  if (!parent) return;
  // Iterate over all child nodes of `parent`.
  for (auto child : parent->children) {
    // Get the i-th child node of `parent`.
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
