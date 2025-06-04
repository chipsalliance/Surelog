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
 * File:   PreprocessFile.cpp
 * Author: alain
 *
 * Created on February 24, 2017, 9:38 PM
 */

#include "Surelog/SourceCompile/PreprocessFile.h"

#include <antlr4-runtime.h>
#include <parser/SV3_1aPpLexer.h>
#include <parser/SV3_1aPpParser.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <iostream>
#include <memory>
#include <regex>
#include <set>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "Surelog/Cache/PPCache.h"
#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/Containers.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Common/PathId.h"
#include "Surelog/Common/Session.h"
#include "Surelog/Common/SymbolId.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/ErrorReporting/ErrorContainer.h"
#include "Surelog/ErrorReporting/ErrorDefinition.h"
#include "Surelog/ErrorReporting/Location.h"
#include "Surelog/ErrorReporting/Waiver.h"
#include "Surelog/Package/Precompiled.h"
#include "Surelog/SourceCompile/CompilationUnit.h"
#include "Surelog/SourceCompile/CompileSourceFile.h"
#include "Surelog/SourceCompile/Compiler.h"
#include "Surelog/SourceCompile/IncludeFileInfo.h"
#include "Surelog/SourceCompile/MacroInfo.h"
#include "Surelog/SourceCompile/SV3_1aPpTreeShapeListener.h"
#include "Surelog/SourceCompile/SV3_1aPreprocessorTreeListener.h"
#include "Surelog/SourceCompile/SymbolTable.h"
#include "Surelog/Utils/StringUtils.h"
#include "Surelog/Utils/Timer.h"

namespace SURELOG {

using antlr4::ANTLRInputStream;
using antlr4::CommonTokenStream;
using antlr4::Parser;
using antlr4::Recognizer;
using antlr4::Token;

const char* const PreprocessFile::MacroNotDefined = "SURELOG_MACRO_NOT_DEFINED";
const char* const PreprocessFile::PP__Line__Marking = "SURELOG__LINE__MARKING";
const char* const PreprocessFile::PP__File__Marking = "SURELOG__FILE__MARKING";

IncludeFileInfo PreprocessFile::s_badIncludeFileInfo(
    IncludeFileInfo::Context::None, IncludeFileInfo::Action::None, BadPathId, 0,
    0, 0, 0, BadSymbolId, 0, 0);

void PreprocessFile::SpecialInstructions::print() {
  std::cout << "Trace:" << (m_mute ? "Mute" : "DontMute")
            << ", EmptyMacro:" << (m_mark_empty_macro ? "Mark" : "DontMark")
            << ", FileLineInfo:"
            << (m_filterFileLine ? "Filter " : "DontFilter") << ", CheckLoop:"
            << (m_check_macro_loop ? "CheckLoop" : "DontCheckLoop")
            << ", AsIsUndefMacro:"
            << (m_as_is_undefined_macro ? "AsIsUndefinedMacro"
                                        : "ComplainUndefinedMacro")
            << ", Evaluate:" << (m_evaluate ? "Evaluate" : "DontEvaluate")
            << std::endl;
}

void PreprocessFile::setDebug(int32_t level) {
  switch (level) {
    case 0:
      m_debugPP = false;
      m_debugPPResult = false;
      m_debugPPTokens = false;
      m_debugPPTree = false;
      m_debugMacro = false;
      m_debugAstModel = false;
      break;
    case 1:
      m_debugPP = false;
      m_debugPPResult = false;
      m_debugPPTokens = false;
      m_debugPPTree = false;
      m_debugMacro = false;
      m_debugAstModel = true;
      break;
    case 2:
      m_debugPP = true;
      m_debugPPResult = false;
      m_debugPPTokens = false;
      m_debugPPTree = false;
      m_debugMacro = true;
      break;
    case 3:
      m_debugPP = true;
      m_debugPPResult = false;
      m_debugPPTokens = true;
      m_debugPPTree = true;
      m_debugMacro = false;
      break;
    case 4:
      m_debugPP = true;
      m_debugPPResult = true;
      m_debugPPTokens = false;
      m_debugPPTree = false;
      m_debugMacro = true;
      break;
    case 5:
      m_debugPP = true;
      m_debugPPResult = true;
      m_debugPPTokens = true;
      m_debugPPTree = true;
      m_debugMacro = true;
      break;
    default:
      break;
  }
}

class PreprocessFile::DescriptiveErrorListener final
    : public antlr4::ANTLRErrorListener {
 public:
  DescriptiveErrorListener(Session* session, PreprocessFile* pp, PathId fileId)
      : m_session(session), m_pp(pp), m_fileId(fileId) {}

  DescriptiveErrorListener(Session* session, PreprocessFile* pp,
                           std::string_view macroContext)
      : m_session(session), m_pp(pp), m_macroContext(macroContext) {}

  void syntaxError(Recognizer* recognizer, Token* offendingSymbol, size_t line,
                   size_t charPositionInLine, const std::string& msg,
                   std::exception_ptr e) override;

  void reportAmbiguity(Parser* recognizer, const antlr4::dfa::DFA& dfa,
                       size_t startIndex, size_t stopIndex, bool exact,
                       const antlrcpp::BitSet& ambigAlts,
                       antlr4::atn::ATNConfigSet* configs) final;

  void reportAttemptingFullContext(Parser* recognizer,
                                   const antlr4::dfa::DFA& dfa,
                                   size_t startIndex, size_t stopIndex,
                                   const antlrcpp::BitSet& conflictingAlts,
                                   antlr4::atn::ATNConfigSet* configs) final;

  void reportContextSensitivity(Parser* recognizer, const antlr4::dfa::DFA& dfa,
                                size_t startIndex, size_t stopIndex,
                                size_t prediction,
                                antlr4::atn::ATNConfigSet* configs) final;

  Session* const m_session = nullptr;
  PreprocessFile* const m_pp;
  const PathId m_fileId;
  const std::string m_macroContext;
  std::vector<std::string> m_fileContent;
};

void PreprocessFile::DescriptiveErrorListener::syntaxError(
    Recognizer* recognizer, Token* offendingSymbol, size_t line,
    size_t charPositionInLine, const std::string& msg, std::exception_ptr e) {
  FileSystem* const fileSystem = m_session->getFileSystem();
  SymbolId msgId = m_pp->registerSymbol(msg);

  if (m_pp->m_macroInfo) {
    std::string lineText(m_pp->getMacroBody());
    for (uint32_t i = 0; i < charPositionInLine; i++) lineText += " ";
    lineText += "^-- " + m_macroContext + ":" + std::to_string(line) + ":" +
                std::to_string(charPositionInLine) + ":";
    msgId = m_pp->registerSymbol(msg + "," + lineText);
    Location loc(m_pp->getMacroInfo()->m_fileId,
                 m_pp->getMacroInfo()->m_startLine + line - 1,
                 charPositionInLine, msgId);
    Location extraLoc(m_pp->getIncluderFileId(m_pp->getIncluderLine()),
                      m_pp->getIncluderLine(), 0);
    Error err(ErrorDefinition::PP_MACRO_SYNTAX_ERROR, loc, extraLoc);
    m_pp->addError(err);
  } else {
    if (m_fileContent.empty()) {
      fileSystem->readLines(m_fileId, m_fileContent);
    }

    std::string lineText;
    if (!m_fileContent.empty() && (line <= m_fileContent.size())) {
      lineText = m_fileContent[line - 1];
      if (!lineText.empty()) {
        if (lineText.back() != '\n') {
          lineText += "\n";
        }
        lineText.append(charPositionInLine, ' ');
        StrAppend(&lineText, "^-- ", fileSystem->toPath(m_fileId), ":", line,
                  ":", charPositionInLine, ":");
      }
    }

    Location loc2(m_pp->registerSymbol(lineText));

    Location loc(m_pp->getFileId(line), line, charPositionInLine, msgId);
    Error err(ErrorDefinition::PP_SYNTAX_ERROR, loc, loc2);
    m_pp->addError(err);
  }
}

void PreprocessFile::DescriptiveErrorListener::reportAmbiguity(
    Parser* recognizer, const antlr4::dfa::DFA& dfa, size_t startIndex,
    size_t stopIndex, bool exact, const antlrcpp::BitSet& ambigAlts,
    antlr4::atn::ATNConfigSet* configs) {}

void PreprocessFile::DescriptiveErrorListener::reportAttemptingFullContext(
    Parser* recognizer, const antlr4::dfa::DFA& dfa, size_t startIndex,
    size_t stopIndex, const antlrcpp::BitSet& conflictingAlts,
    antlr4::atn::ATNConfigSet* configs) {}

void PreprocessFile::DescriptiveErrorListener::reportContextSensitivity(
    Parser* recognizer, const antlr4::dfa::DFA& dfa, size_t startIndex,
    size_t stopIndex, size_t prediction, antlr4::atn::ATNConfigSet* configs) {}

PreprocessFile::PreprocessFile(Session* session, PathId fileId,
                               CompileSourceFile* csf,
                               SpecialInstructions& instructions,
                               CompilationUnit* comp_unit, Library* library,
                               PreprocessFile* includer /* = nullptr */,
                               uint32_t includerLine /* = 0 */)
    : m_session(session),
      m_fileId(fileId),
      m_library(library),
      m_includer(includer),
      m_includerLine(includerLine),
      m_compileSourceFile(csf),
      m_lineCount(0),
      m_antlrParserHandler(nullptr),
      m_instructions(instructions),
      m_listener(nullptr),
      m_macroInfo(nullptr),
      m_compilationUnit(comp_unit),
      m_pauseAppend(false),
      m_usingCachedVersion(false),
      m_embeddedMacroCallLine(0),
      m_embeddedMacroCallColumn(0),
      m_fileContent(nullptr),
      m_verilogVersion(VerilogVersion::NoVersion) {
  setDebug(m_session->getCommandLineParser()->getDebugLevel());
  if (m_includer != nullptr) {
    m_includer->m_includes.push_back(this);
  }
}

PreprocessFile::PreprocessFile(Session* session, SymbolId macroId,
                               CompileSourceFile* csf,
                               SpecialInstructions& instructions,
                               CompilationUnit* comp_unit, Library* library,
                               PreprocessFile* includer, uint32_t includerLine,
                               std::string_view macroBody, MacroInfo* macroInfo,
                               PathId fileId, PathId embeddedMacroCallFile,
                               uint32_t embeddedMacroCallLine,
                               uint16_t embeddedMacroCallColumn)
    : m_session(session),
      m_fileId(fileId),
      m_macroId(macroId),
      m_library(library),
      m_macroBody(macroBody),
      m_includer(includer),
      m_includerLine(includerLine),
      m_compileSourceFile(csf),
      m_lineCount(0),
      m_antlrParserHandler(nullptr),
      m_instructions(instructions),
      m_listener(nullptr),
      m_macroInfo(macroInfo),
      m_compilationUnit(comp_unit),
      m_pauseAppend(false),
      m_usingCachedVersion(false),
      m_embeddedMacroCallFile(embeddedMacroCallFile),
      m_embeddedMacroCallLine(embeddedMacroCallLine),
      m_embeddedMacroCallColumn(embeddedMacroCallColumn),
      m_fileContent(nullptr),
      m_verilogVersion(VerilogVersion::NoVersion) {
  setDebug(m_session->getCommandLineParser()->getDebugLevel());
  if (m_includer != nullptr) {
    m_includer->m_includes.push_back(this);
  }
}

void PreprocessFile::addError(Error& error) {
  if (!m_instructions.m_mute) m_session->getErrorContainer()->addError(error);
}

std::string_view PreprocessFile::getSymbol(SymbolId id) const {
  return m_session->getSymbolTable()->getSymbol(id);
}

SymbolId PreprocessFile::getMacroSignature() {
  std::ostringstream strm;
  strm << getSymbol(m_macroId);
  if (m_macroInfo) {
    strm << "|" << m_session->getFileSystem()->toPath(m_macroInfo->m_fileId)
         << "|" << std::to_string(m_macroInfo->m_startLine);
  }
  strm << "|" << m_macroBody;
  SymbolId sigId = registerSymbol(strm.str());
  return sigId;
}

PreprocessFile::~PreprocessFile() {
  delete m_listener;
  if (!m_instructions.m_persist) {
    for (auto& info : m_includeFileInfo) {
      DeleteSequenceContainerPointersAndClear(&info.m_macroDefinitions);
      info.m_macroDefinition = nullptr;
    }
    m_includeFileInfo.clear();
  }
}

PreprocessFile::AntlrParserHandler::~AntlrParserHandler() {
  delete m_errorListener;
  // delete m_pptree;  // INVALID MEMORY READ can be seen in AdvancedDebug
  if (m_clearAntlrCache) {
    m_pplexer->getInterpreter<antlr4::atn::LexerATNSimulator>()->clearDFA();
    m_ppparser->getInterpreter<antlr4::atn::ParserATNSimulator>()->clearDFA();
  }
  delete m_ppparser;
  delete m_pptokens;
  delete m_pplexer;
  delete m_inputStream;
}

bool PreprocessFile::preprocess() {
  m_result.clear();
  FileSystem* const fileSystem = m_session->getFileSystem();
  Precompiled* const precompiled = m_session->getPrecompiled();
  CommandLineParser* const clp = m_session->getCommandLineParser();
  const bool isPrecompiled = precompiled->isFilePrecompiled(m_fileId);

  std::string macroName;
  Timer tmr;
  SymbolId macroSignatureId;
  if (m_macroBody.empty()) {
    PPCache cache(m_session, this);
    if (cache.restore(clp->lowMem() || clp->noCacheHash())) {
      m_usingCachedVersion = true;
      getCompilationUnit()->setCurrentTimeInfo(getFileId(0));
      if (m_debugAstModel && !isPrecompiled && m_macroBody.empty()) {
        std::cout << m_fileContent->printObjects() << std::endl;
      }
      if (isPrecompiled || clp->noCacheHash()) {
        if (clp->debugCache()) {
          std::cout << "PP CACHE USED FOR: " << PathIdPP(m_fileId, fileSystem)
                    << std::endl;
        }
        return true;
      }
      if (!clp->parseOnly() && !clp->lowMem()) {
        clearIncludeFileInfo();
      }
    }
  } else {
    macroName = getSymbol(m_macroId);
    macroSignatureId = getMacroSignature();
  }
  if (clp->parseOnly() || clp->lowMem() || clp->link()) return true;

  m_antlrParserHandler =
      m_macroBody.empty()
          ? getCompileSourceFile()->getAntlrPpHandlerForId(m_fileId)
          : getCompileSourceFile()->getAntlrPpHandlerForId(macroSignatureId);

  if (m_antlrParserHandler == nullptr) {
    m_antlrParserHandler = new AntlrParserHandler();
    m_antlrParserHandler->m_clearAntlrCache = clp->lowMem();
    if (m_macroBody.empty()) {
      if (m_debugPP)
        std::cout << "PP PREPROCESS FILE: " << PathIdPP(m_fileId, fileSystem)
                  << std::endl;
      std::istream& stream = fileSystem->openForRead(m_fileId);
      if (!stream.good()) {
        fileSystem->close(stream);

        if (m_includer == nullptr) {
          Location loc(m_fileId);
          Error err(ErrorDefinition::PP_CANNOT_OPEN_FILE, loc);
          addError(err);
        } else {
          Location includeFile(m_includer->m_fileId, m_includerLine, 0,
                               (SymbolId)m_fileId);
          Error err(ErrorDefinition::PP_CANNOT_OPEN_INCLUDE_FILE, includeFile);
          addError(err);
        }
        return false;
      }
      // Remove ^M (DOS) from text file
      std::string text;
      std::streamsize length = 0;
      if (fileSystem->filesize(m_fileId, &length)) {
        text.reserve(length);
      }
      char nonAscii = '\0';
      int32_t lineNb = 1;
      int32_t columnNb = 0;
      int32_t lineNonAscii = 0;
      int32_t columnNonAscii = 0;
      int32_t c = stream.get();
      while (stream.good()) {
        if (c != '\r') {
          if (std::isprint(c) || std::isspace(c)) {
            text += static_cast<char>(c);
          } else {
            if (nonAscii == '\0') {
              nonAscii = c;
              lineNonAscii = lineNb;
              columnNonAscii = columnNb;
            }
            text += " ";
          }
        }
        if (c == '\n') {
          lineNb++;
          columnNb = 0;
        }
        columnNb++;
        c = stream.get();
      }
      fileSystem->close(stream);

      if (nonAscii != '\0') {
        std::string symbol;
        if (!clp->pythonAllowed()) symbol = std::string(1, nonAscii);
        if (m_includer == nullptr) {
          Location loc(m_fileId, lineNonAscii, columnNonAscii,
                       registerSymbol(symbol));
          Error err(ErrorDefinition::PP_NON_ASCII_CONTENT, loc);
          addError(err);
        } else {
          Location loc(m_fileId, lineNonAscii, 0, registerSymbol(symbol));
          Location includeFile(m_includer->m_fileId, m_includerLine, 0);
          Error err(ErrorDefinition::PP_NON_ASCII_CONTENT, loc, includeFile);
          addError(err);
        }
      }

      try {
        m_antlrParserHandler->m_inputStream = new ANTLRInputStream(text);
      } catch (...) {
        Location loc(BadSymbolId);
        if (m_includer == nullptr) {
          Location file(m_fileId);
          loc = file;
        } else {
          Location includeFile(m_includer->m_fileId, m_includerLine, 0,
                               (SymbolId)m_fileId);
          loc = includeFile;
        }
        Error err(ErrorDefinition::PP_CANNOT_READ_FILE_CONTENT, loc);
        addError(err);
        return false;
      }
    } else {
      if (m_debugPP) {
        std::cout << "PP PREPROCESS MACRO: " << m_macroBody << std::endl;
      }
      m_antlrParserHandler->m_inputStream = new ANTLRInputStream(m_macroBody);
    }
    if (m_macroBody.empty()) {
      m_antlrParserHandler->m_errorListener =
          new PreprocessFile::DescriptiveErrorListener(m_session, this,
                                                       m_fileId);
    } else {
      m_antlrParserHandler->m_errorListener =
          new PreprocessFile::DescriptiveErrorListener(m_session, this,
                                                       "in macro " + macroName);
    }
    m_antlrParserHandler->m_pplexer =
        new SV3_1aPpLexer(m_antlrParserHandler->m_inputStream);
    m_antlrParserHandler->m_pplexer->removeErrorListeners();
    m_antlrParserHandler->m_pplexer->addErrorListener(
        m_antlrParserHandler->m_errorListener);
    m_antlrParserHandler->m_pptokens =
        new CommonTokenStream(m_antlrParserHandler->m_pplexer);
    m_antlrParserHandler->m_pptokens->fill();

    if (clp->profile()) {
      // m_profileInfo += "Tokenizer: " + std::to_string (tmr.elapsed_rounded
      // ())
      // + " " + fileName + "\n";
      tmr.reset();
    }

    if (m_debugPPTokens) {
      std::cout << "PP TOKENS: " << std::endl;
      for (auto token : m_antlrParserHandler->m_pptokens->getTokens()) {
        std::cout << token->toString() << std::endl;
      }
    }

    m_antlrParserHandler->m_ppparser =
        new SV3_1aPpParser(m_antlrParserHandler->m_pptokens);
    m_antlrParserHandler->m_ppparser
        ->getInterpreter<antlr4::atn::ParserATNSimulator>()
        ->setPredictionMode(antlr4::atn::PredictionMode::SLL);
    m_antlrParserHandler->m_ppparser->removeErrorListeners();
    m_antlrParserHandler->m_ppparser->setErrorHandler(
        std::make_shared<antlr4::BailErrorStrategy>());
    try {
      m_antlrParserHandler->m_pptree =
          m_antlrParserHandler->m_ppparser->top_level_rule();

      if (m_macroBody.empty() && clp->profile()) {
        StrAppend(&m_profileInfo, "PP SSL Parsing: ",
                  StringUtils::to_string(tmr.elapsed_rounded()), "s ",
                  fileSystem->toPath(m_fileId), "\n");
        tmr.reset();
      }
    } catch (antlr4::ParseCancellationException&) {
      m_antlrParserHandler->m_pptokens->reset();
      m_antlrParserHandler->m_ppparser->reset();
      m_antlrParserHandler->m_ppparser->addErrorListener(
          m_antlrParserHandler->m_errorListener);
      m_antlrParserHandler->m_ppparser->setErrorHandler(
          std::make_shared<antlr4::DefaultErrorStrategy>());
      m_antlrParserHandler->m_ppparser
          ->getInterpreter<antlr4::atn::ParserATNSimulator>()
          ->setPredictionMode(antlr4::atn::PredictionMode::LL);
      m_antlrParserHandler->m_pptree =
          m_antlrParserHandler->m_ppparser->top_level_rule();

      if (m_macroBody.empty() && clp->profile()) {
        StrAppend(&m_profileInfo, "PP LL  Parsing: ",
                  StringUtils::to_string(tmr.elapsed_rounded()), "s ",
                  fileSystem->toPath(m_fileId), "\n");
        tmr.reset();
      }
    }

    if (m_debugPPTree)
      std::cout << "PP TREE: "
                << m_antlrParserHandler->m_pptree->toStringTree(
                       m_antlrParserHandler->m_ppparser)
                << std::endl
                << std::endl;

    if (m_macroBody.empty()) {
      getCompileSourceFile()->registerAntlrPpHandlerForId(m_fileId,
                                                          m_antlrParserHandler);
    } else {
      getCompileSourceFile()->registerAntlrPpHandlerForId(macroSignatureId,
                                                          m_antlrParserHandler);
    }
  }
  m_result.clear();
  m_lineCount = 0;
  delete m_listener;

  if (clp->parseTree()) {
    m_listener = new SV3_1aPreprocessorTreeListener(
        m_session, this, m_antlrParserHandler->m_pptokens, m_instructions);
  } else {
    m_listener = new SV3_1aPpTreeShapeListener(
        m_session, this, m_antlrParserHandler->m_pptokens, m_instructions);
  }

  int32_t indexOpposite = -1;
  if (m_macroBody.empty() && (m_includer == nullptr)) {
    indexOpposite = getSourceFile()->addIncludeFileInfo(
        /* context */ IncludeFileInfo::Context::Include,
        /* action */ IncludeFileInfo::Action::Push,
        /* macroDefinition */ nullptr,
        /* sectionFileId */ m_fileId,
        /* sectionLine */ 1,
        /* sectionColumn */ 1,
        /* sourceLine */ 1,
        /* sourceColumn */ 1,
        /* sectionSymbolId */ BadSymbolId,
        /* symbolLine */ 0,
        /* symbolColumn */ 0);
  }

  // TODO: this leaks
  antlr4::tree::ParseTreeWalker::DEFAULT.walk(m_listener,
                                              m_antlrParserHandler->m_pptree);

  if (m_macroBody.empty() && (m_includer == nullptr)) {
    const auto [lastLine, lastColumn] = getCurrentPosition();
    getSourceFile()->addIncludeFileInfo(
        /* context */ IncludeFileInfo::Context::Include,
        /* action */ IncludeFileInfo::Action::Pop,
        /* macroDefinition */ nullptr,
        /* sectionFileId */ m_fileId,
        /* sectionLine */ lastLine,
        /* sectionColumn */ lastColumn,
        /* sourceLine */ lastLine,
        /* sourceColumn */ lastColumn,
        /* sectionSymbolId */ BadSymbolId,
        /* symbolLine */ 0,
        /* symbolColumn */ 0,
        /* indexOpposite */ indexOpposite);
  }

  if (m_debugAstModel && !isPrecompiled && m_macroBody.empty()) {
    std::cout << m_fileContent->printObjects() << std::endl;
  }
  m_lineCount = std::count(m_result.cbegin(), m_result.cend(), '\n');
  return true;
}

LineColumn PreprocessFile::getCurrentPosition() const {
  uint32_t line = 0;
  uint16_t column = 0;
  bool columnReady = false;
  const PreprocessFile* pf = this;

  while (pf != nullptr) {
    line += pf->m_lineCount;
    if (!columnReady && !pf->m_result.empty()) {
      if (std::string::size_type p = pf->m_result.rfind('\n');
          p != std::string::npos) {
        column += pf->m_result.length() - p;
        columnReady = true;
      } else {
        column += pf->m_result.length();
      }
    }
    pf = pf->m_includer;
  }

  if (column == 0) column = 1;
  return LineColumn(line + 1, column);
}

int32_t PreprocessFile::addIncludeFileInfo(
    IncludeFileInfo::Context context, IncludeFileInfo::Action action,
    const MacroInfo* macroDefinition, PathId sectionFileId,
    uint32_t sectionLine, uint16_t sectionColumn, uint32_t sourceLine,
    uint16_t sourceColumn, SymbolId symbolId, uint32_t symbolLine,
    uint16_t symbolColumn, int32_t indexOpposite /* = -1 */) {
  const int32_t index = m_includeFileInfo.size();
  m_includeFileInfo.emplace_back(context, action, macroDefinition,
                                 sectionFileId, sectionLine, sectionColumn,
                                 sourceLine, sourceColumn, symbolId, symbolLine,
                                 symbolColumn, indexOpposite);
  if ((action == IncludeFileInfo::Action::Pop) && (indexOpposite >= 0)) {
    m_includeFileInfo[indexOpposite].m_indexOpposite = index;
  }
  return index;
}

void PreprocessFile::clearIncludeFileInfo() { m_includeFileInfo.clear(); }

void PreprocessFile::append(std::string_view s) {
  if (!m_pauseAppend) {
    m_lineCount += std::count(s.cbegin(), s.cend(), '\n');
    m_result.append(s);
  }
}

MacroInfo* PreprocessFile::defineMacro(
    std::string_view name, MacroInfo::DefType defType, uint32_t startLine,
    uint16_t startColumn, uint32_t endLine, uint16_t endColumn,
    uint16_t nameStartColumn, uint16_t bodyStartColumn,
    std::string_view arguments,
    const std::vector<LineColumn>& argumentPositions,
    const std::vector<std::string>& tokens,
    const std::vector<LineColumn>& tokenPositions) {
  // *** Argument processing
  std::string_view arguments_short = StringUtils::trim(arguments);
  // Remove (
  if (!arguments_short.empty() && (arguments_short.front() == '(')) {
    arguments_short.remove_prefix(1);
  }
  // Remove )
  if (!arguments_short.empty() && (arguments_short.back() == ')')) {
    arguments_short.remove_suffix(1);
  }
  // Tokenize args
  std::vector<std::string> args;
  StringUtils::tokenize(arguments_short, ",", args);

  if (m_debugMacro) {
    std::string body;
    for (const auto& token : tokens) {
      body += token;
    }
    std::cout << "PP RECORDING MACRO: " << name << ": | " << body << " | "
              << std::endl;
  }

  std::vector<std::string> body_tokens;
  body_tokens.reserve(tokens.size());
  std::vector<LineColumn> token_positions;
  token_positions.reserve(tokenPositions.size());

  for (size_t i = 0, ni = tokens.size(); i < ni; ++i) {
    const std::string& tok = tokens[i];
    const LineColumn& lc = tokenPositions[i];
    if (tok == "``_``") {
      body_tokens.emplace_back("``");
      body_tokens.emplace_back("_");
      body_tokens.emplace_back("``");
      token_positions.emplace_back(lc.first, lc.second);
      token_positions.emplace_back(lc.first, lc.second + 2);
      token_positions.emplace_back(lc.first, lc.second + 3);
    } else {
      body_tokens.emplace_back(tok);
      token_positions.emplace_back(lc);
    }
  }

  const std::vector<std::string> old_body_tokens(body_tokens);
  StringUtils::replaceInTokenVector(body_tokens, "`\"", "\"");
  StringUtils::replaceInTokenVector(body_tokens, "`\\`\"", "\\\"");

  // Adjust the body tokens based on the replace calls above
  if (!token_positions.empty()) {
    std::vector<LineColumn> new_token_positions;
    new_token_positions.reserve(token_positions.size());
    for (size_t i = 0, ni = body_tokens.size(); i < ni; ++i) {
      size_t offset = (old_body_tokens[i].length() - body_tokens[i].length());
      new_token_positions.emplace_back(token_positions[i].first,
                                       token_positions[i].second + offset);
    }
    token_positions = std::move(new_token_positions);
  }

  // std::cout << "PP RECORDING MACRO: " << name  << ", FILE: " <<
  // getSymbol(getFileId(line)) << "" << std::endl;

  MacroInfo* macroInfo =
      new MacroInfo(name, defType, getFileId(startLine), startLine, startColumn,
                    endLine, endColumn, nameStartColumn, bodyStartColumn, args,
                    argumentPositions, body_tokens, token_positions);
  m_macros.emplace_back(macroInfo);
  m_compilationUnit->registerMacroInfo(macroInfo);
  checkMacroArguments_(name, startLine, nameStartColumn, args, tokens);

  int32_t pops = 0;
  std::vector<IncludeFileInfo>& includeFileInfo =
      getSourceFile()->m_includeFileInfo;
  for (int32_t i = includeFileInfo.size() - 1; i >= 0; --i) {
    IncludeFileInfo& info = includeFileInfo[i];
    if (info.m_context == IncludeFileInfo::Context::Include) {
      if (info.m_action == IncludeFileInfo::Action::Push) {
        if (pops-- == 0) {
          info.m_macroDefinitions.emplace_back(macroInfo);
          break;
        }
      } else if (info.m_action == IncludeFileInfo::Action::Pop) {
        ++pops;
      }
    }
  }

  return macroInfo;
}

void PreprocessFile::addMacro(MacroInfo* info) {
  // NOTE: This is called from PPCache so all the inputs are already processed.
  m_macros.emplace_back(info);
  m_compilationUnit->registerMacroInfo(info);
}

void PreprocessFile::checkMacroArguments_(
    std::string_view name, uint32_t line, uint16_t column,
    const std::vector<std::string>& arguments,
    const std::vector<std::string>& tokens) {
  std::set<std::string_view, std::less<>> argSet;
  std::set<std::string, std::less<>> tokenSet;
  for (const auto& s : arguments) {
    argSet.emplace(
        StringUtils::trim(StringUtils::rtrim_until(StringUtils::trim(s), '=')));
  }
  for (const auto& s : tokens) {
    std::string tok(StringUtils::trim(s));
    tok = StringUtils::replaceAll(tok, "``", "");
    tok = StringUtils::replaceAll(tok, "`", "");
    tokenSet.emplace(tok);
  }
  for (const auto& s : argSet) {
    if (tokenSet.find(s) == tokenSet.end()) {
      Location loc(m_fileId, line, column, registerSymbol(s));
      Error err(ErrorDefinition::PP_MACRO_UNUSED_ARGUMENT, loc);
      addError(err);
    }
  }
  for (uint32_t i = 0; i < tokens.size(); i++) {
    std::string s1 = tokens[i];
    std::string s2 = tokens[i];
    bool check = false;
    if ((s1.find("``") != std::string::npos) && (s1 != "``"))  // ``a``
    {
      s1 = std::regex_replace(s1, std::regex("``"), "");
      s2 = s1;
      check = true;
    } else if (s1 == "``") {
      if (i > 0) s1 = tokens[i - 1];
      s1 = StringUtils::trim(s1);
      s2 = tokens[i + 1];
      s2 = StringUtils::trim(s2);
      check = true;
    }
    if (check) {
      if ((argSet.find(s1) == argSet.end()) &&
          (argSet.find(s2) == argSet.end())) {
        for (auto s : {s1, s2}) {
          if (argSet.find(s) == argSet.end()) {
            if (s.find('`') != std::string::npos) continue;
            if (s.find("//") != std::string::npos) continue;
            if (!std::isalpha(s[0])) continue;
            Location loc(m_fileId, line, column, registerSymbol(s));
            Error err(ErrorDefinition::PP_MACRO_UNDEFINED_ARGUMENT, loc);
            addError(err);
          }
        }
      }
    }
  }
}

void PreprocessFile::reportIncludeInfo(std::ostream& strm) const {
  for (size_t i = 0, ni = m_includeFileInfo.size(); i < ni; ++i) {
    const IncludeFileInfo& ifi = m_includeFileInfo[i];
    const bool isInclude = ifi.m_context == IncludeFileInfo::Context::Include;
    std::string_view symbol;
    if (ifi.m_action == IncludeFileInfo::Action::Push) {
      symbol =
          isInclude ? getSymbol(ifi.m_symbolId) : ifi.m_macroDefinition->m_name;
    } else {
      const IncludeFileInfo& oifi = m_includeFileInfo[ifi.m_indexOpposite];
      symbol = isInclude ? getSymbol(oifi.m_symbolId)
                         : oifi.m_macroDefinition->m_name;
    }
    strm << std::right << std::setw(3) << i
         << ": Context: " << (isInclude ? "INCLUDE" : "  MARCO") << ", Action: "
         << (ifi.m_action == IncludeFileInfo::Action::Pop ? " POP" : "PUSH")
         << ", Source: [" << std::right << std::setw(4) << ifi.m_sourceLine
         << "," << std::right << std::setw(4) << ifi.m_sourceColumn
         << "], Section: [" << std::right << std::setw(4) << ifi.m_sectionLine
         << "," << std::right << std::setw(4) << ifi.m_sectionColumn
         << "], Symbol: [" << std::right << std::setw(4) << ifi.m_symbolLine
         << "," << std::right << std::setw(4) << ifi.m_symbolColumn << "] "
         << symbol << std::endl;
  }
}

PathId PreprocessFile::getIncluderFileId(uint32_t line) const {
  const PreprocessFile* tmp = this;
  while (tmp->m_includer != nullptr) {
    tmp = tmp->m_includer;
  }
  return tmp->getFileId(line);
}

PreprocessFile* PreprocessFile::getSourceFile() {
  PreprocessFile* tmp = this;
  while (tmp->m_includer != nullptr) {
    tmp = tmp->m_includer;
  }
  return tmp;
}

void PreprocessFile::forgetPreprocessor_(PreprocessFile* inc,
                                         PreprocessFile* pp) {
  for (std::vector<PreprocessFile*>::iterator itr = inc->m_includes.begin();
       itr != inc->m_includes.end(); itr++) {
    if ((*itr) == pp) {
      inc->m_includes.erase(itr);
      break;
    }
  }
}

SymbolId PreprocessFile::registerSymbol(std::string_view symbol) const {
  return m_session->getSymbolTable()->registerSymbol(symbol);
}

SymbolId PreprocessFile::getId(std::string_view symbol) const {
  return m_session->getSymbolTable()->getId(symbol);
}

std::string PreprocessFile::evaluateMacroInstance(
    std::string_view macro_instance, PreprocessFile* callingFile,
    uint32_t callingLine, uint16_t callingColumn,
    SpecialInstructions::CheckLoopInstr checkMacroLoop,
    SpecialInstructions::AsIsUndefinedMacroInstr asisUndefMacro) {
  std::string result;
  // SymbolId macroArgs = registerSymbol (macro_instance);
  SpecialInstructions instructions(
      SpecialInstructions::Mute, SpecialInstructions::Mark,
      SpecialInstructions::Filter, checkMacroLoop, asisUndefMacro);
  PreprocessFile* pp = new PreprocessFile(
      m_session, BadSymbolId, m_compileSourceFile, instructions,
      callingFile ? callingFile->m_compilationUnit
                  : m_includer->m_compilationUnit,
      callingFile ? callingFile->m_library : m_includer->m_library,
      callingFile ? callingFile : m_includer, callingLine, macro_instance,
      nullptr, BadPathId, m_fileId, callingLine, callingColumn);
  if (!pp->preprocess()) {
    result = MacroNotDefined;
  } else {
    result = std::get<0>(pp->getPreProcessedFileContent());
  }
  forgetPreprocessor_(m_includer ? m_includer : callingFile, pp);
  delete pp;
  return result;
}

static std::string_view getFirstNonEmptyToken(
    const std::vector<std::string>& tokens) {
  for (const auto& token : tokens) {
    if (token != " ") return token;
  }
  static constexpr std::string_view kEmpty;
  return kEmpty;
}

std::tuple<bool, std::string, std::vector<LineColumn>, LineColumn>
PreprocessFile::evaluateMacro_(
    std::string_view name, std::vector<std::string>& actual_args,
    PreprocessFile* callingFile, uint32_t callingLine, LoopCheck& loopChecker,
    MacroInfo* macroInfo, SpecialInstructions& instructions,
    PathId embeddedMacroCallFile, uint32_t embeddedMacroCallLine,
    uint16_t embeddedMacroCallColumn) {
  FileSystem* const fileSystem = m_session->getFileSystem();

  if (instructions.m_check_macro_loop) {
    bool loop = loopChecker.addEdge(callingFile->m_macroId, getId(name));
    if (loop) {
      std::vector<SymbolId> loop = loopChecker.reportLoop();
      for (const auto& id : loop) {
        MacroInfo* macroInfo2 = m_compilationUnit->getMacroInfo(getSymbol(id));
        if (macroInfo2) {
          Location loc(macroInfo2->m_fileId, macroInfo2->m_startLine,
                       macroInfo2->m_nameStartColumn, id);
          Location exloc(macroInfo->m_fileId, macroInfo->m_startLine,
                         macroInfo->m_nameStartColumn, getId(name));
          Error err(ErrorDefinition::PP_RECURSIVE_MACRO_DEFINITION, loc, exloc);
          addError(err);
          return {false, "", {}, {0, 0}};
        }
      }
    }
  }
  std::string result;
  bool found = false;
  LineColumn sectionEnd;
  const std::vector<std::string>& formal_args = macroInfo->m_arguments;
  // Don't modify the actual tokens of the macro, make a copy...
  std::vector<std::string> body_tokens(macroInfo->m_tokens);

  if ((actual_args.size() > formal_args.size() && (!m_instructions.m_mute))) {
    if (formal_args.empty() && (getFirstNonEmptyToken(body_tokens) == "(")) {
      Location loc(macroInfo->m_fileId, macroInfo->m_startLine,
                   macroInfo->m_nameStartColumn + name.size() + 1, getId(name));
      Error err(ErrorDefinition::PP_MACRO_HAS_SPACE_BEFORE_ARGS, loc);
      addError(err);
    } else if ((!Waiver::macroArgCheck(name)) && !formal_args.empty()) {
      Location loc(callingFile->getFileId(callingLine),
                   callingFile->getLineNb(callingLine), 0, getId(name));
      Location arg(BadPathId, 0, 0,
                   registerSymbol(std::to_string(actual_args.size())));
      Location def(macroInfo->m_fileId, macroInfo->m_startLine,
                   macroInfo->m_nameStartColumn,
                   registerSymbol(std::to_string(formal_args.size())));
      Error err(ErrorDefinition::PP_TOO_MANY_ARGS_MACRO, {loc, arg, def});
      addError(err);
    }
  }

  bool incorrectArgNb = false;
  static const std::regex ws_re("[ \t]+");
  for (uint32_t i = 0; i < formal_args.size(); i++) {
    std::vector<std::string> formal_arg_default;
    StringUtils::tokenize(formal_args[i], "=", formal_arg_default);
    const std::string formal =
        std::regex_replace(formal_arg_default[0], ws_re, "");
    bool empty_actual = true;
    if (i < actual_args.size()) {
      for (char c : actual_args[i]) {
        if (c != ' ') {
          empty_actual = false;
          break;
        }
      }
    }
    if (!empty_actual) {
      if (actual_args[i] == SymbolTable::getEmptyMacroMarker()) {
        actual_args[i].clear();
      }

      const std::string pattern = "`" + formal;
      StringUtils::replaceInTokenVector(body_tokens, {"``", pattern, "``"},
                                        "`" + actual_args[i]);
      StringUtils::replaceInTokenVector(body_tokens, {"``", formal, "``"},
                                        actual_args[i]);
      StringUtils::replaceInTokenVector(body_tokens, "``" + formal + "``",
                                        actual_args[i]);
      StringUtils::replaceInTokenVector(body_tokens, {formal, "``"},
                                        actual_args[i]);
      StringUtils::replaceInTokenVector(body_tokens, {"``", formal},
                                        actual_args[i]);
      StringUtils::replaceInTokenVector(body_tokens, {formal, " ", "``"},
                                        actual_args[i]);
      StringUtils::replaceInTokenVector(body_tokens, formal + "``",
                                        actual_args[i]);
      StringUtils::replaceInTokenVector(body_tokens, formal, actual_args[i]);
    } else if (formal_arg_default.size() == 2) {
      const std::string default_val =
          std::regex_replace(formal_arg_default[1], ws_re, "");
      StringUtils::replaceInTokenVector(body_tokens, {"``", formal, "``"},
                                        default_val);
      StringUtils::replaceInTokenVector(body_tokens, "``" + formal + "``",
                                        default_val);
      StringUtils::replaceInTokenVector(body_tokens, {formal, "``"},
                                        default_val);
      StringUtils::replaceInTokenVector(body_tokens, {"``", formal},
                                        default_val);
      StringUtils::replaceInTokenVector(body_tokens, {formal, " ", "``"},
                                        default_val);
      StringUtils::replaceInTokenVector(body_tokens, formal + "``",
                                        default_val);
      StringUtils::replaceInTokenVector(body_tokens, formal, default_val);
    } else {
      StringUtils::replaceInTokenVector(body_tokens, {"``", formal, "``"}, "");
      StringUtils::replaceInTokenVector(body_tokens, "``" + formal + "``", "");
      StringUtils::replaceInTokenVector(body_tokens, {formal, "``"}, "");
      StringUtils::replaceInTokenVector(body_tokens, {"``", formal}, "");
      StringUtils::replaceInTokenVector(body_tokens, {formal, " ", "``"}, "");
      StringUtils::replaceInTokenVector(body_tokens, formal + "``", "");
      StringUtils::replaceInTokenVector(body_tokens, formal, "");

      if ((int32_t)i > (int32_t)(((int32_t)actual_args.size()) - 1)) {
        if (!instructions.m_mute) {
          Location loc(callingFile->getFileId(callingLine),
                       callingFile->getLineNb(callingLine), 0, getId(name));
          SymbolId id =
              registerSymbol(std::to_string(i + 1) + " (" + formal + ")");
          Location arg(id);
          Location def(macroInfo->m_fileId, macroInfo->m_startLine,
                       macroInfo->m_nameStartColumn, id);
          Error err(ErrorDefinition::PP_MACRO_NO_DEFAULT_VALUE,
                    {loc, arg, def});
          addError(err);
        }
        incorrectArgNb = true;
      }
    }
  }
  if (incorrectArgNb) {
    return {true, StrCat("`", name), {{1, 1}}, {1, name.length() + 2}};
  }

  std::string body;
  std::vector<LineColumn> token_positions;
  token_positions.reserve(macroInfo->m_tokenPositions.size());
  uint32_t pos = 1;
  uint32_t line = 0;
  for (size_t i = 0, ni = body_tokens.size(); i < ni; ++i) {
    const auto& token = body_tokens[i];
    body += token;
    if ((line == 0) || (macroInfo->m_tokenPositions[i].first != line)) {
      line = macroInfo->m_tokenPositions[i].first;
      pos = 1;
    }
    token_positions.emplace_back(line - macroInfo->m_startLine + 1, pos);
    pos += token.length();
  }

  if (!actual_args.empty() && formal_args.empty()) {
    body += "(";
    body += actual_args[0];
    body += ")";
  }
  // *** Body processing
  std::string body_short;
  body_short.reserve(body.length());
  // Replace \\n by \n
  bool inString = false;
  char previous = '\0';
  for (char c : body) {
    if (c == '"') {
      inString = !inString;
    }
    if ((previous == '\\') && (c == '\n') && (!inString)) {
      body_short.pop_back();
    }
    body_short += c;
    previous = c;
  }

  if (body_short.find('`') != std::string::npos) {
    // Recursively resolve macro instantiation within the macro
    if (m_debugMacro) {
      std::cout << "PP BODY EXPANSION FOR " << name
                << " in : " << fileSystem->toPath(m_fileId) << std::endl;
      for (const auto& arg : actual_args) {
        std::cout << "PP ARG: " << arg << "\n";
      }
    }
    SymbolId macroId = registerSymbol(name);
    SpecialInstructions instructions(
        m_instructions.m_mute, SpecialInstructions::DontMark,
        SpecialInstructions::Filter, m_instructions.m_check_macro_loop,
        m_instructions.m_as_is_undefined_macro);
    PreprocessFile* pp = new PreprocessFile(
        m_session, macroId, m_compileSourceFile, instructions,
        callingFile ? callingFile->m_compilationUnit
                    : m_includer->m_compilationUnit,
        callingFile ? callingFile->m_library : m_includer->m_library,
        callingFile ? callingFile : m_includer, callingLine, body_short,
        macroInfo, macroInfo->m_fileId, embeddedMacroCallFile,
        embeddedMacroCallLine, embeddedMacroCallColumn);
    getCompileSourceFile()->registerPP(pp);
    if (!pp->preprocess()) {
      result = MacroNotDefined;
    } else {
      std::string pp_result = std::get<0>(pp->getPreProcessedFileContent());
      if (callingLine && callingFile && !callingFile->isMacroBody()) {
        CommandLineParser* const clp = m_session->getCommandLineParser();
        pp_result = std::regex_replace(
            pp_result, std::regex(PP__File__Marking),
            StrCat("\"",
                   fileSystem->toPath(callingFile->getFileId(callingLine)),
                   "\""));
        if (clp->disableLineMarkings()) {
          pp_result =
              std::regex_replace(pp_result, std::regex(PP__Line__Marking), "0");
        } else {
          pp_result =
              std::regex_replace(pp_result, std::regex(PP__Line__Marking),
                                 std::to_string(callingLine));
        }
      }
      result = pp_result;
      found = true;

      sectionEnd.first = macroInfo->m_endLine;
      const size_t pos = pp_result.find_last_of('\n');
      if (pos == std::string::npos) {
        sectionEnd.second = macroInfo->m_bodyStartColumn + pp_result.length();
      } else {
        sectionEnd.second = pp_result.length() - pos;
      }
    }
  } else {
    sectionEnd.first = macroInfo->m_endLine;
    const size_t pos = body_short.find_last_of('\n');
    if (pos == std::string::npos) {
      sectionEnd.second = macroInfo->m_bodyStartColumn + body_short.length();
    } else {
      sectionEnd.second = body_short.length() - pos;
    }
    result = body_short;
    found = true;
  }
  return {found, result, token_positions, sectionEnd};
}

MacroInfo* PreprocessFile::getMacro(std::string_view name) {
  registerSymbol(name);
  return m_compilationUnit->getMacroInfo(name);
}

MacroInfo* PreprocessFile::undefineMacro(std::string_view name,
                                         uint32_t startLine,
                                         uint16_t startColumn, uint32_t endLine,
                                         uint16_t endColumn,
                                         uint16_t nameStartColumn) {
  /*SymbolId macroId = */ registerSymbol(name);
  if (m_debugMacro)
    std::cout << "PP CALL TO deleteMacro for " << name << std::endl;
  return defineMacro(name, MacroInfo::DefType::UndefineOne, startLine,
                     startColumn, endLine, endColumn, nameStartColumn, 0, "",
                     {}, {}, {});
}

MacroInfo* PreprocessFile::undefineAllMacros(uint32_t startLine,
                                             uint16_t startColumn,
                                             uint32_t endLine,
                                             uint16_t endColumn) {
  if (m_debugMacro) std::cout << "PP CALL TO undefineAllMacros" << std::endl;
  return defineMacro("", MacroInfo::DefType::UndefineAll, startLine,
                     startColumn, endLine, endColumn, 0, 0, "", {}, {}, {});
}

std::tuple<bool, std::string, std::vector<LineColumn>, LineColumn>
PreprocessFile::getMacro(
    std::string_view name, std::vector<std::string>& arguments,
    PreprocessFile* callingFile, uint32_t callingLine, LoopCheck& loopChecker,
    SpecialInstructions& instructions, PathId embeddedMacroCallFile,
    uint32_t embeddedMacroCallLine, uint16_t embeddedMacroCallColumn) {
  CommandLineParser* const clp = m_session->getCommandLineParser();
  SymbolId macroId = registerSymbol(name);
  if (m_debugMacro) {
    std::cout << "PP CALL TO getMacro for " << name << "\n";
    for (const auto& arg : arguments) {
      std::cout << "PP ARG: " << arg << "\n";
    }
    instructions.print();
  }

  MacroInfo* info = m_compilationUnit->getMacroInfo(name);

  // Try CommandLine overrides
  const auto& defines = clp->getDefineList();
  auto itMap = defines.find(macroId);
  if (itMap != defines.end()) {
    const std::string& result = itMap->second;

    size_t bodyStartLine = 0;
    size_t bodyStartColumn = 0;
    if (info != nullptr) {
      bodyStartLine = info->m_startLine;
      bodyStartColumn = info->m_bodyStartColumn - 1;
    }

    return {true,
            result,
            {{bodyStartLine, name.length() - result.length()}},
            {bodyStartLine, bodyStartColumn + result.length() + 1}};
  }

  // Try local file scope
  if (info != nullptr) {
    if (instructions.m_evaluate == SpecialInstructions::Evaluate) {
      auto [succeeded, result, positions, sectionEnd] =
          evaluateMacro_(name, arguments, callingFile, callingLine, loopChecker,
                         info, instructions, embeddedMacroCallFile,
                         embeddedMacroCallLine, embeddedMacroCallColumn);
      if (succeeded) {
        result = std::regex_replace(result, std::regex("``"), "");
        return {true, result, positions, sectionEnd};
      }
    } else {
      return {true, "", {}, {info->m_endLine, info->m_endColumn}};
    }
  }

  if (instructions.m_as_is_undefined_macro ==
      SpecialInstructions::AsIsUndefinedMacro) {
    return {true, StrCat("`", name), {{1, 1}}, {1, name.length() + 2}};
  }

  return {
      false, MacroNotDefined, {{1, 1}}, {1, std::strlen(MacroNotDefined) + 1}};
}

PathId PreprocessFile::getFileId(uint32_t line) const {
  const uint32_t size = m_lineTranslationVec.size();
  if (isMacroBody() && m_macroInfo) {
    return m_macroInfo->m_fileId;
  } else {
    if (size) {
      if (size == 1) {
        if (line >= m_lineTranslationVec[0].m_originalLine) {
          return (m_lineTranslationVec[0].m_pretendFileId);
        }
      } else {
        uint32_t index = size - 1;
        while (true) {
          if (line >= m_lineTranslationVec[index].m_originalLine) {
            return (m_lineTranslationVec[index].m_pretendFileId);
          }
          if (index == 0) break;
          index--;
        }
      }
      return m_fileId;
    } else {
      return m_fileId;
    }
  }
}

uint32_t PreprocessFile::getLineNb(uint32_t line) {
  if (isMacroBody() && m_macroInfo) {
    return (m_macroInfo->m_startLine + line - 1);
  } else if (!m_lineTranslationVec.empty()) {
    uint32_t index = m_lineTranslationVec.size() - 1;
    while (true) {
      if (line >= m_lineTranslationVec[index].m_originalLine) {
        return (m_lineTranslationVec[index].m_pretendLine +
                (line - m_lineTranslationVec[index].m_originalLine));
      }
      if (index == 0) break;
      index--;
    }
  }
  return line;
}

std::tuple<const std::string&, LineColumn>
PreprocessFile::getPreProcessedFileContent() const {
  if (m_debugPPResult) {
    FileSystem* const fileSystem = m_session->getFileSystem();
    std::string objName =
        m_macroBody.empty()
            ? std::string("file ").append(fileSystem->toPath(m_fileId))
            : std::string("macro ").append(m_macroBody);
    std::cout << "PP RESULT for " << objName
              << " : \nvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv\n"
              << m_result << "\n^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n"
              << std::endl;
  }
  const size_t pos = m_result.find_last_of('\n');
  const LineColumn sectionEnd = {
      std::max<size_t>(m_lineCount, 1),
      (pos == std::string::npos) ? m_result.length() : m_result.length() - pos};
  return {m_result, sectionEnd};
}

PreprocessFile::IfElseStack& PreprocessFile::getStack() {
  PreprocessFile* tmp = this;
  while (tmp->m_includer != nullptr) {
    tmp = tmp->m_includer;
  }
  // std::cout << "STACK FOR: " << tmp->m_fileName << std::endl;
  return tmp->m_ifStack;
}

void PreprocessFile::collectIncludedFiles(std::set<PreprocessFile*>& included) {
  for (PreprocessFile* include : m_includes) {
    if (!include->isMacroBody()) {
      included.insert(include);
    }
    include->collectIncludedFiles(included);
  }
}

void PreprocessFile::saveCache() {
  CommandLineParser* clp = m_session->getCommandLineParser();
  if (clp->parseOnly() || clp->lowMem() || clp->link()) return;
  if (m_macroBody.empty()) {
    if (!m_usingCachedVersion) {
      PPCache cache(m_session, this);
      cache.save();
    }
  }
  // Disable cache saving for include files
  // If an include file is multiply included in a compilation unit with
  // different outcomes for the content of the file (GUARDING) The cache saved
  // is incorrect.

  // for (PreprocessFile* include : m_includes) {
  //  include->saveCache();
  // }
}
}  // namespace SURELOG
