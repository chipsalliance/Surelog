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
 * File:   AntlrParserErrorListener.cpp
 * Author: alain
 *
 * Created on July 29, 2017, 5:32 PM
 */
#include "antlr4-runtime.h"
#include "atn/ParserATNSimulator.h"
using namespace std;
using namespace antlr4;
#include "SourceCompile/SymbolTable.h"
#include "CommandLine/CommandLineParser.h"
#include "ErrorReporting/ErrorContainer.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/Compiler.h"
#include "SourceCompile/ParseFile.h"
#include "Utils/FileUtils.h"
#include "Utils/StringUtils.h"
#include "SourceCompile/AntlrParserErrorListener.h"
using namespace SURELOG;

void AntlrParserErrorListener::syntaxError(Recognizer *recognizer,
                                           Token *offendingSymbol, size_t line,
                                           size_t charPositionInLine,
                                           const std::string &msg,
                                           std::exception_ptr e) {
  if (m_watchDogOn) {
    m_barked = true;
    return;
  }
  if (m_fileContent.empty()) {
    m_fileContent = FileUtils::getFileContent(m_fileName);
  }

  std::string lineText;
  if (!m_fileContent.empty()) {
    lineText = StringUtils::getLineInString(m_fileContent, line);
    if (!lineText.empty()) {
      if (!strstr(lineText.c_str(), "\n")) {
        lineText += "\n";
      }
      for (unsigned int i = 0; i < charPositionInLine; i++) lineText += " ";
      lineText += "^-- " + m_fileName + ":" + std::to_string(line) +
                  ":" + std::to_string(charPositionInLine) + ":";
    }
  }
  if (m_reportedSyntaxError == false) {
    SymbolId msgId = m_parser->registerSymbol(msg);
    int adjustedLine = m_parser->getLineNb(line + m_lineOffset);
    Location loc(m_parser->getFileId(line + m_lineOffset), adjustedLine,
                 charPositionInLine, msgId);
    Location loc2(0, 0, 0, m_parser->registerSymbol(lineText));
    Error err(ErrorDefinition::PA_SYNTAX_ERROR, loc, loc2);
    m_parser->addError(err);
    m_reportedSyntaxError = true;
  }
}

void AntlrParserErrorListener::reportAmbiguity(
    Parser *recognizer, const dfa::DFA &dfa, size_t startIndex,
    size_t stopIndex, bool exact, const antlrcpp::BitSet &ambigAlts,
    atn::ATNConfigSet *configs) {}

void AntlrParserErrorListener::reportAttemptingFullContext(
    Parser *recognizer, const dfa::DFA &dfa, size_t startIndex,
    size_t stopIndex, const antlrcpp::BitSet &conflictingAlts,
    atn::ATNConfigSet *configs) {}

void AntlrParserErrorListener::reportContextSensitivity(
    Parser *recognizer, const dfa::DFA &dfa, size_t startIndex,
    size_t stopIndex, size_t prediction, atn::ATNConfigSet *configs) {}
