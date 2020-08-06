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

#ifndef ANTLRPARSERHANDLER_H
#define ANTLRPARSERHANDLER_H

#include "parser/SV3_1aLexer.h"
#include "parser/SV3_1aParser.h"
#include "antlr4-runtime.h"

namespace SURELOG {

class AntlrParserErrorListener;

class AntlrParserHandler {
 public:
  AntlrParserHandler()
      : m_inputStream(NULL),
        m_lexer(NULL),
        m_tokens(NULL),
        m_parser(NULL),
        m_tree(NULL),
        m_errorListener(NULL) {}
  ~AntlrParserHandler();
  antlr4::ANTLRInputStream* m_inputStream;
  SV3_1aLexer* m_lexer;
  antlr4::CommonTokenStream* m_tokens;
  SV3_1aParser* m_parser;
  antlr4::tree::ParseTree* m_tree;
  AntlrParserErrorListener* m_errorListener;
};

};  // namespace SURELOG

#endif /* ANTLRPARSERHANDLER_H */
