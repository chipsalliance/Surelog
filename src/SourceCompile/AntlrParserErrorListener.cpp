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

#include <Surelog/Common/FileSystem.h>
#include <Surelog/ErrorReporting/ErrorContainer.h>
#include <Surelog/SourceCompile/AntlrParserErrorListener.h>
#include <Surelog/SourceCompile/CompileSourceFile.h>
#include <Surelog/SourceCompile/ParseFile.h>
#include <Surelog/SourceCompile/SymbolTable.h>
#include <Surelog/Utils/StringUtils.h>

namespace SURELOG {

void AntlrParserErrorListener::syntaxError(
    antlr4::Recognizer *recognizer, antlr4::Token *offendingSymbol, size_t line,
    size_t charPositionInLine, const std::string &msg, std::exception_ptr e) {
  if (m_watchDogOn) {
    m_barked = true;
    return;
  }
  FileSystem *const fileSystem = FileSystem::getInstance();
  if (m_fileContent.empty()) {
    fileSystem->readLines(m_fileId, m_fileContent);
  }

  std::string lineText;
  if (!m_fileContent.empty() && (line <= m_fileContent.size())) {
    lineText = m_fileContent[line - 1];
    if (!lineText.empty()) {
      lineText.push_back('\n');
      lineText.append(charPositionInLine, ' ');
      StrAppend(&lineText, "^-- ", fileSystem->toPath(m_fileId), ":", line, ":",
                charPositionInLine, ":");
    }
  }
  if (m_reportedSyntaxError == false) {
    SymbolId msgId = m_parser->registerSymbol(msg);
    int adjustedLine = m_parser->getLineNb(line + m_lineOffset);
    Location loc1(m_parser->getFileId(line + m_lineOffset), adjustedLine,
                  charPositionInLine, msgId);
    Location loc2(m_parser->registerSymbol(lineText));
    Location loc3(m_parser->getCompileSourceFile()->getFileId(), 0, 0);
    Error err(ErrorDefinition::PA_SYNTAX_ERROR, {loc1, loc2, loc3});
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
