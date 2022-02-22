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

#include <Surelog/ErrorReporting/ErrorContainer.h>
#include <Surelog/SourceCompile/AntlrParserErrorListener.h>
#include <Surelog/SourceCompile/ParseFile.h>
#include <Surelog/Utils/FileUtils.h>
#include <Surelog/Utils/StringUtils.h>

namespace SURELOG {

void AntlrParserErrorListener::syntaxError(
    antlr4::Recognizer *recognizer, antlr4::Token *offendingSymbol, size_t line,
    size_t charPositionInLine, const std::string &msg, std::exception_ptr e) {
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
      if (lineText.find('\n') == std::string::npos) {
        lineText += "\n";
      }
      for (unsigned int i = 0; i < charPositionInLine; i++) lineText += " ";
      lineText += "^-- " + m_fileName + ":" + std::to_string(line) + ":" +
                  std::to_string(charPositionInLine) + ":";
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
    antlr4::Parser *recognizer, const antlr4::dfa::DFA &dfa, size_t startIndex,
    size_t stopIndex, bool exact, const antlrcpp::BitSet &ambigAlts,
    antlr4::atn::ATNConfigSet *configs) {}

void AntlrParserErrorListener::reportAttemptingFullContext(
    antlr4::Parser *recognizer, const antlr4::dfa::DFA &dfa, size_t startIndex,
    size_t stopIndex, const antlrcpp::BitSet &conflictingAlts,
    antlr4::atn::ATNConfigSet *configs) {}

void AntlrParserErrorListener::reportContextSensitivity(
    antlr4::Parser *recognizer, const antlr4::dfa::DFA &dfa, size_t startIndex,
    size_t stopIndex, size_t prediction, antlr4::atn::ATNConfigSet *configs) {}

}  // namespace SURELOG
