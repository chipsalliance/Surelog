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

#include "antlr4-runtime.h"
using namespace std;
using namespace antlr4;
#include "parser/SV3_1aLexer.h"
#include "parser/SV3_1aParser.h"

#include "SourceCompile/AntlrParserHandler.h"

using namespace SURELOG;

AntlrParserHandler::~AntlrParserHandler() {
  //  delete m_tree; // INVALID MEMORY READ can be seen in AdvancedDebug
  delete m_parser;
  delete m_tokens;
  delete m_lexer;
  delete m_inputStream;
}
