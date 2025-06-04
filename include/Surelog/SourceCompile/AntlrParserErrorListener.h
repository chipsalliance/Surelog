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
#include <Surelog/Common/PathId.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

namespace SURELOG {
class ParseFile;
class Session;

class AntlrParserErrorListener final : public antlr4::ANTLRErrorListener {
 public:
  AntlrParserErrorListener(Session *session, ParseFile *parser, bool watchDogOn,
                           uint32_t lineOffset, PathId fileId);
  ~AntlrParserErrorListener() final = default;

  void syntaxError(antlr4::Recognizer *recognizer,
                   antlr4::Token *offendingSymbol, size_t line,
                   size_t charPositionInLine, const std::string &msg,
                   std::exception_ptr e) final;

  void reportAmbiguity(antlr4::Parser *recognizer, const antlr4::dfa::DFA &dfa,
                       size_t startIndex, size_t stopIndex, bool exact,
                       const antlrcpp::BitSet &ambigAlts,
                       antlr4::atn::ATNConfigSet *configs) final;

  void reportAttemptingFullContext(antlr4::Parser *recognizer,
                                   const antlr4::dfa::DFA &dfa,
                                   size_t startIndex, size_t stopIndex,
                                   const antlrcpp::BitSet &conflictingAlts,
                                   antlr4::atn::ATNConfigSet *configs) final;

  void reportContextSensitivity(antlr4::Parser *recognizer,
                                const antlr4::dfa::DFA &dfa, size_t startIndex,
                                size_t stopIndex, size_t prediction,
                                antlr4::atn::ATNConfigSet *configs) final;

  Session *const m_session = nullptr;
  ParseFile *m_parser = nullptr;
  int32_t m_reportedSyntaxError = 0;
  bool m_watchDogOn = false;
  bool m_barked = false;
  uint32_t m_lineOffset = 0;
  PathId m_fileId;
  std::vector<std::string> m_fileContent;
  bool m_printExtraPpLineInfo;
};

};  // namespace SURELOG

#endif /* SURELOG_ANTLRPARSERERRORLISTENER_H */
