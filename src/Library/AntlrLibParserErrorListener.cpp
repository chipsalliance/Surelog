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
 * File:   AntlrLibParserErrorListener.cpp
 * Author: alain
 *
 * Created on Feb 08, 2018, 9:54 PM
 */
#include "antlr4-runtime.h"
#include "atn/ParserATNSimulator.h"
using namespace std;
using namespace antlr4;
#include "SourceCompile/SymbolTable.h"
#include "Design/FileContent.h"
#include "CommandLine/CommandLineParser.h"
#include "ErrorReporting/ErrorContainer.h"
#include "Library/ParseLibraryDef.h"
#include "Library/AntlrLibParserErrorListener.h"
using namespace SURELOG;

void AntlrLibParserErrorListener::syntaxError(
    Recognizer *recognizer, Token *offendingSymbol, size_t line,
    size_t charPositionInLine, const std::string &msg, std::exception_ptr e) {
  SymbolId msgId = m_parser->getSymbolTable()->registerSymbol(msg);
  Location loc(m_parser->getFileId(), line, charPositionInLine, msgId);
  Error err(ErrorDefinition::PA_SYNTAX_ERROR, loc);
  m_parser->getErrorContainer()->addError(err);
}

void AntlrLibParserErrorListener::reportAmbiguity(
    Parser *recognizer, const dfa::DFA &dfa, size_t startIndex,
    size_t stopIndex, bool exact, const antlrcpp::BitSet &ambigAlts,
    atn::ATNConfigSet *configs) {}

void AntlrLibParserErrorListener::reportAttemptingFullContext(
    Parser *recognizer, const dfa::DFA &dfa, size_t startIndex,
    size_t stopIndex, const antlrcpp::BitSet &conflictingAlts,
    atn::ATNConfigSet *configs) {}

void AntlrLibParserErrorListener::reportContextSensitivity(
    Parser *recognizer, const dfa::DFA &dfa, size_t startIndex,
    size_t stopIndex, size_t prediction, atn::ATNConfigSet *configs) {}
