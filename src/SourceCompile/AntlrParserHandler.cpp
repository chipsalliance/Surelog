
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
 * File:   AntlrParserHandler.cpp
 * Author: alain
 *
 * Created on June 4, 2017, 4:21 PM
 */

#include "Surelog/SourceCompile/AntlrParserHandler.h"

#include <antlr4-runtime.h>
#include <parser/SV3_1aLexer.h>
#include <parser/SV3_1aParser.h>

#include "Surelog/SourceCompile/AntlrParserErrorListener.h"  // IWYU pragma: keep

namespace SURELOG {

AntlrParserHandler::~AntlrParserHandler() {
  delete m_errorListener;
  // ParseTree is deleted in antlr4::ParseTreeTracker
  // delete m_tree; // INVALID MEMORY READ can be seen in AdvancedDebug
  if (m_clearAntlrCache) {
    m_lexer->getInterpreter<antlr4::atn::LexerATNSimulator>()->clearDFA();
    m_parser->getInterpreter<antlr4::atn::ParserATNSimulator>()->clearDFA();
  }
  delete m_parser;
  delete m_tokens;
  delete m_lexer;
  delete m_inputStream;
}
}  // namespace SURELOG
