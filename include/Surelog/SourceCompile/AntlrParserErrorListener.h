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
 * File:   AntlrParserErrorListener.h
 * Author: alain
 *
 * Created on July 29, 2017, 5:32 PM
 */

#ifndef SURELOG_ANTLRPARSERERRORLISTENER_H
#define SURELOG_ANTLRPARSERERRORLISTENER_H
#pragma once

#include <ANTLRErrorListener.h>

namespace SURELOG {

class ParseFile;

class AntlrParserErrorListener : public antlr4::ANTLRErrorListener {
 public:
  AntlrParserErrorListener(ParseFile *parser, bool watchDogOn,
                           unsigned int lineOffset, const std::string &fileName)
      : m_parser(parser),
        m_reportedSyntaxError(false),
        m_watchDogOn(watchDogOn),
        m_barked(false),
        m_lineOffset(lineOffset),
        m_fileName(fileName) {}

  ~AntlrParserErrorListener() override{};

  void syntaxError(antlr4::Recognizer *recognizer,
                   antlr4::Token *offendingSymbol, size_t line,
                   size_t charPositionInLine, const std::string &msg,
                   std::exception_ptr e) override;

  void reportAmbiguity(antlr4::Parser *recognizer, const antlr4::dfa::DFA &dfa,
                       size_t startIndex, size_t stopIndex, bool exact,
                       const antlrcpp::BitSet &ambigAlts,
                       antlr4::atn::ATNConfigSet *configs) override;

  void reportAttemptingFullContext(antlr4::Parser *recognizer,
                                   const antlr4::dfa::DFA &dfa,
                                   size_t startIndex, size_t stopIndex,
                                   const antlrcpp::BitSet &conflictingAlts,
                                   antlr4::atn::ATNConfigSet *configs) override;

  void reportContextSensitivity(antlr4::Parser *recognizer,
                                const antlr4::dfa::DFA &dfa, size_t startIndex,
                                size_t stopIndex, size_t prediction,
                                antlr4::atn::ATNConfigSet *configs) override;

  ParseFile *m_parser;
  bool m_reportedSyntaxError;
  bool m_watchDogOn;
  bool m_barked;
  unsigned int m_lineOffset;
  std::string m_fileName;
  std::string m_fileContent;
};

};  // namespace SURELOG

#endif /* SURELOG_ANTLRPARSERERRORLISTENER_H */
