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
 * File:   AntlrParserHandler.h
 * Author: alain
 *
 * Created on June 4, 2017, 4:21 PM
 */

#ifndef SURELOG_ANTLRPARSERHANDLER_H
#define SURELOG_ANTLRPARSERHANDLER_H
#pragma once

namespace antlr4 {
class ANTLRInputStream;
class CommonTokenStream;

namespace tree {
class ParseTree;
}
}  // namespace antlr4

namespace SURELOG {

class AntlrParserErrorListener;
class SV3_1aLexer;
class SV3_1aParser;

class AntlrParserHandler {
 public:
  AntlrParserHandler() = default;
  ~AntlrParserHandler();

  antlr4::ANTLRInputStream* m_inputStream = nullptr;
  SV3_1aLexer* m_lexer = nullptr;
  antlr4::CommonTokenStream* m_tokens = nullptr;
  SV3_1aParser* m_parser = nullptr;
  antlr4::tree::ParseTree* m_tree = nullptr;
  AntlrParserErrorListener* m_errorListener = nullptr;
};

};  // namespace SURELOG

#endif /* SURELOG_ANTLRPARSERHANDLER_H */
