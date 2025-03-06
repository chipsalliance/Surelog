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
#include <string_view>
#include <utility>
#include <vector>

#include "Surelog/Cache/PPCache.h"
#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Common/PathId.h"
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
    IncludeFileInfo::Context::NONE, 0, BadSymbolId, BadPathId, 0, 0, 0, 0,
    IncludeFileInfo::Action::NONE);

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
  DescriptiveErrorListener(PreprocessFile* pp, PathId fileId)
      : m_pp(pp), m_fileId(fileId) {}
  DescriptiveErrorListener(PreprocessFile* pp, std::string_view macroContext)
      : m_pp(pp), m_macroContext(macroContext) {}

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

  PreprocessFile* const m_pp;
  const PathId m_fileId;
  const std::string m_macroContext;
  std::vector<std::string> m_fileContent;
};

void PreprocessFile::DescriptiveErrorListener::syntaxError(
    Recognizer* recognizer, Token* offendingSymbol, size_t line,
    size_t charPositionInLine, const std::string& msg, std::exception_ptr e) {
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
    FileSystem* fileSystem = FileSystem::getInstance();
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

PreprocessFile::PreprocessFile(PathId fileId, CompileSourceFile* csf,
                               SpecialInstructions& instructions,
                               CompilationUnit* comp_unit, Library* library,
                               PreprocessFile* includer /* = nullptr */,
                               uint32_t includerLine /* = 0 */)
    : m_fileId(fileId),
      m_library(library),
      m_includer(includer),
      m_includerLine(includerLine),
      m_compileSourceFile(csf),
      m_lineCount(0),
      m_listener(nullptr),
      m_instructions(instructions),
      m_antlrParserHandler(nullptr),
      m_macroInfo(nullptr),
      m_compilationUnit(comp_unit),
      m_pauseAppend(false),
      m_usingCachedVersion(false),
      m_embeddedMacroCallLine(0),
      m_fileContent(nullptr),
      m_verilogVersion(VerilogVersion::NoVersion) {
  setDebug(m_compileSourceFile->m_commandLineParser->getDebugLevel());
  resetIncludeFileInfo();
  if (m_includer != nullptr) {
    m_includer->m_includes.push_back(this);
  }
}

PreprocessFile::PreprocessFile(SymbolId macroId, CompileSourceFile* csf,
                               SpecialInstructions& instructions,
                               CompilationUnit* comp_unit, Library* library,
                               PreprocessFile* includer, uint32_t includerLine,
                               std::string_view macroBody, MacroInfo* macroInfo,
                               uint32_t embeddedMacroCallLine,
                               PathId embeddedMacroCallFile)
    : m_macroId(macroId),
      m_library(library),
      m_macroBody(macroBody),
      m_includer(includer),
      m_includerLine(includerLine),
      m_compileSourceFile(csf),
      m_lineCount(0),
      m_listener(nullptr),
      m_instructions(instructions),
      m_antlrParserHandler(nullptr),
      m_macroInfo(macroInfo),
      m_compilationUnit(comp_unit),
      m_pauseAppend(false),
      m_usingCachedVersion(false),
      m_embeddedMacroCallLine(embeddedMacroCallLine),
      m_embeddedMacroCallFile(embeddedMacroCallFile),
      m_fileContent(nullptr),
      m_verilogVersion(VerilogVersion::NoVersion) {
  setDebug(m_compileSourceFile->m_commandLineParser->getDebugLevel());
  if (m_includer != nullptr) {
    m_includer->m_includes.push_back(this);
  }
}

void PreprocessFile::addError(Error& error) {
  if (!m_instructions.m_mute)
    getCompileSourceFile()->getErrorContainer()->addError(error);
}

std::string_view PreprocessFile::getSymbol(SymbolId id) const {
  return getCompileSourceFile()->getSymbolTable()->getSymbol(id);
}

SymbolId PreprocessFile::getMacroSignature() {
  FileSystem* const fileSystem = FileSystem::getInstance();
  std::ostringstream strm;
  strm << getSymbol(m_macroId);
  if (m_macroInfo) {
    strm << "|" << fileSystem->toPath(m_macroInfo->m_fileId) << "|"
         << std::to_string(m_macroInfo->m_startLine);
  }
  strm << "|" << m_macroBody;
  SymbolId sigId = registerSymbol(strm.str());
  return sigId;
}

PreprocessFile::~PreprocessFile() {
  delete m_listener;
  if (!m_instructions.m_persist) {
    for (auto& [name, macros] : m_macros) {
      for (auto& macro : macros) {
        delete macro;
      }
    }
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

static size_t LinesCount(std::string_view s) {
  return std::count(s.begin(), s.end(), '\n');
}

bool PreprocessFile::preprocess() {
  m_result.clear();
  std::string macroName;
  CommandLineParser* clp = getCompileSourceFile()->getCommandLineParser();
  FileSystem* const fileSystem = FileSystem::getInstance();
  Timer tmr;
  bool precompiled = false;
  SymbolId macroSignatureId;
  if (m_macroBody.empty()) {
    precompiled = Precompiled::getSingleton()->isFilePrecompiled(
        m_fileId, getCompileSourceFile()->getSymbolTable());
    PPCache cache(this);
    if (cache.restore(clp->lowMem() || clp->noCacheHash())) {
      m_usingCachedVersion = true;
      getCompilationUnit()->setCurrentTimeInfo(getFileId(0));
      if (m_debugAstModel && !precompiled)
        std::cout << m_fileContent->printObjects();
      if (precompiled || clp->noCacheHash()) {
        if (clp->debugCache()) {
          std::cout << "PP CACHE USED FOR: " << PathIdPP(m_fileId) << std::endl;
        }
        return true;
      }
      if (!clp->parseOnly() && !clp->lowMem()) {
        resetIncludeFileInfo();
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
        std::cout << "PP PREPROCESS FILE: " << PathIdPP(m_fileId) << std::endl;
      std::istream& stream = fileSystem->openForRead(m_fileId);
      if (!stream.good()) {
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
      char nonAscii = '\0';
      char c = stream.get();
      int32_t lineNb = 1;
      int32_t columnNb = 0;
      int32_t lineNonAscii = 0;
      int32_t columnNonAscii = 0;
      while (stream.good()) {
        if (c != 0x0D) {
          if (isascii(c))
            text += c;
          else {
            nonAscii = c;
            lineNonAscii = lineNb;
            columnNonAscii = columnNb;
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
          new PreprocessFile::DescriptiveErrorListener(this, m_fileId);
    } else {
      m_antlrParserHandler->m_errorListener =
          new PreprocessFile::DescriptiveErrorListener(this,
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

    if (getCompileSourceFile()->getCommandLineParser()->profile()) {
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

      if (m_macroBody.empty() &&
          getCompileSourceFile()->getCommandLineParser()->profile()) {
        StrAppend(&m_profileInfo, "PP SSL Parsing: ",
                  StringUtils::to_string(tmr.elapsed_rounded()), "s ",
                  fileSystem->toPath(m_fileId), "\n");
        tmr.reset();
      }
    } catch (antlr4::ParseCancellationException& pex) {
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

      if (m_macroBody.empty() &&
          getCompileSourceFile()->getCommandLineParser()->profile()) {
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
  m_listener = new SV3_1aPpTreeShapeListener(
      this, m_antlrParserHandler->m_pptokens, m_instructions);
  // TODO: this leaks
  antlr4::tree::ParseTreeWalker::DEFAULT.walk(m_listener,
                                              m_antlrParserHandler->m_pptree);
  if (m_debugAstModel && !precompiled)
    std::cout << m_fileContent->printObjects();
  m_lineCount = LinesCount(m_result);
  return true;
}

uint32_t PreprocessFile::getSumLineCount() {
  uint32_t total = m_lineCount;
  if (m_includer) total += m_includer->getSumLineCount();
  return total;
}

int32_t PreprocessFile::addIncludeFileInfo(
    IncludeFileInfo::Context context, uint32_t sectionStartLine,
    SymbolId sectionSymbolId, PathId sectionFileId, uint32_t originalStartLine,
    uint32_t originalStartColumn, uint32_t originalEndLine,
    uint32_t originalEndColumn, IncludeFileInfo::Action action,
    int32_t indexOpening /* = 0 */, int32_t indexClosing /* = 0 */) {
  int32_t index = m_includeFileInfo.size();
  m_includeFileInfo.emplace_back(
      context, sectionStartLine, sectionSymbolId, sectionFileId,
      originalStartLine, originalStartColumn, originalEndLine,
      originalEndColumn, action, indexOpening, indexClosing);
  return index;
}

void PreprocessFile::resetIncludeFileInfo() {
  clearIncludeFileInfo();
  if ((!m_compileSourceFile->m_commandLineParser->parseOnly()) &&
      (!m_compileSourceFile->m_commandLineParser->lowMem())) {
    addIncludeFileInfo(IncludeFileInfo::Context::NONE, 0, BadSymbolId, m_fileId,
                       0, 0, 0, 0, IncludeFileInfo::Action::POP, 0, 0);
  }
}

void PreprocessFile::clearIncludeFileInfo() { m_includeFileInfo.clear(); }

void PreprocessFile::append(std::string_view s) {
  if (!m_pauseAppend) {
    m_lineCount += LinesCount(s);
    m_result.append(s);
  }
}

void PreprocessFile::recordMacro(std::string_view name, uint32_t startLine,
                                 uint16_t startColumn, uint32_t endLine,
                                 uint16_t endColumn, std::string_view arguments,
                                 const std::vector<std::string>& tokens) {
  // *** Argument processing
  std::string arguments_short(arguments);
  // Remove (
  size_t p = arguments_short.find('(');
  if (p != std::string::npos) {
    arguments_short.erase(p, 1);
  }
  // Remove )
  p = arguments_short.find(')');
  if (p != std::string::npos) {
    arguments_short.erase(p, 1);
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

  // std::cout << "PP RECORDING MACRO: " << name  << ", FILE: " <<
  // getSymbol(getFileId(line)) << "" << std::endl;

  MacroInfo* macroInfo = new MacroInfo(
      name, arguments.empty() ? MacroInfo::NO_ARGS : MacroInfo::WITH_ARGS,
      getFileId(startLine), startLine, startColumn, endLine, endColumn, args,
      tokens);
  MacroStorageRef::iterator itr = m_macros.find(name);
  if (itr == m_macros.end()) {
    itr = m_macros.emplace(name, std::vector<MacroInfo*>()).first;
  }
  itr->second.push_back(macroInfo);
  m_compilationUnit->registerMacroInfo(name, macroInfo);
  checkMacroArguments_(name, startLine, startColumn, args, tokens);
}

std::string PreprocessFile::reportIncludeInfo() const {
  FileSystem* const fileSystem = FileSystem::getInstance();
  std::ostringstream strm;
  for (auto const& info : m_includeFileInfo) {
    const char* const context =
        (info.m_context == IncludeFileInfo::Context::INCLUDE) ? "inc" : "mac";
    const char* const action =
        (info.m_action == IncludeFileInfo::Action::PUSH) ? "in" : "out";
    strm << context << " " << info.m_originalStartLine << ","
         << info.m_originalStartColumn << ":" << info.m_originalEndLine << ","
         << info.m_originalEndColumn << " " << getSymbol(info.m_sectionSymbolId)
         << "^" << fileSystem->toPath(info.m_sectionFileId) << " "
         << info.m_sectionStartLine << " " << action << std::endl;
  }
  return strm.str();
}

void PreprocessFile::recordMacro(std::string_view name, PathId fileId,
                                 uint32_t startLine, uint16_t startColumn,
                                 uint32_t endLine, uint16_t endColumn,
                                 const std::vector<std::string>& arguments,
                                 const std::vector<std::string>& tokens) {
  MacroInfo* macroInfo = new MacroInfo(
      name, arguments.empty() ? MacroInfo::NO_ARGS : MacroInfo::WITH_ARGS,
      fileId, startLine, startColumn, endLine, endColumn, arguments, tokens);
  MacroStorageRef::iterator itr = m_macros.find(name);
  if (itr == m_macros.end()) {
    itr = m_macros.emplace(name, std::vector<MacroInfo*>()).first;
  }
  itr->second.push_back(macroInfo);
  m_compilationUnit->registerMacroInfo(name, macroInfo);
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
    tokenSet.insert(tok);
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
  return getCompileSourceFile()->getSymbolTable()->registerSymbol(symbol);
}

SymbolId PreprocessFile::getId(std::string_view symbol) const {
  return getCompileSourceFile()->getSymbolTable()->getId(symbol);
}

std::string PreprocessFile::evaluateMacroInstance(
    std::string_view macro_instance, PreprocessFile* callingFile,
    uint32_t callingLine, SpecialInstructions::CheckLoopInstr checkMacroLoop,
    SpecialInstructions::AsIsUndefinedMacroInstr asisUndefMacro) {
  std::string result;
  // SymbolId macroArgs = registerSymbol (macro_instance);
  SpecialInstructions instructions(
      SpecialInstructions::Mute, SpecialInstructions::Mark,
      SpecialInstructions::Filter, checkMacroLoop, asisUndefMacro);
  PreprocessFile* pp =
      new PreprocessFile(BadSymbolId, m_compileSourceFile, instructions,
                         m_includer ? m_includer->m_compilationUnit
                                    : callingFile->m_compilationUnit,
                         callingFile->m_library, /* includer */ nullptr,
                         /* includerLine */ 0, macro_instance);
  if (!pp->preprocess()) {
    result = MacroNotDefined;
  } else {
    result = pp->getPreProcessedFileContent();
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

std::pair<bool, std::string> PreprocessFile::evaluateMacro_(
    std::string_view name, std::vector<std::string>& actual_args,
    PreprocessFile* callingFile, uint32_t callingLine, LoopCheck& loopChecker,
    MacroInfo* macroInfo, SpecialInstructions& instructions,
    uint32_t embeddedMacroCallLine, PathId embeddedMacroCallFile) {
  FileSystem* const fileSystem = FileSystem::getInstance();
  std::string result;
  bool found = false;
  const std::vector<std::string>& formal_args = macroInfo->m_arguments;
  const std::vector<std::string>& orig_body_tokens = macroInfo->m_tokens;

  if (instructions.m_check_macro_loop) {
    bool loop = loopChecker.addEdge(callingFile->m_macroId, getId(name));
    if (loop) {
      std::vector<SymbolId> loop = loopChecker.reportLoop();
      for (const auto& id : loop) {
        MacroInfo* macroInfo2 = m_compilationUnit->getMacroInfo(getSymbol(id));
        if (macroInfo2) {
          Location loc(macroInfo2->m_fileId, macroInfo2->m_startLine,
                       macroInfo2->m_startColumn, id);
          Location exloc(macroInfo->m_fileId, macroInfo->m_startLine,
                         macroInfo->m_startColumn, getId(name));
          Error err(ErrorDefinition::PP_RECURSIVE_MACRO_DEFINITION, loc, exloc);
          addError(err);
          return std::make_pair(false,
                                std::string(SymbolTable::getBadSymbol()));
        }
      }
    }
  }
  // Don't modify the actual tokens of the macro, make a copy...
  std::vector<std::string> body_tokens;
  for (const std::string& tok : orig_body_tokens) {
    if (tok == "``_``") {
      body_tokens.push_back("``");
      body_tokens.push_back("_");
      body_tokens.push_back("``");
    } else {
      body_tokens.push_back(tok);
    }
  }

  StringUtils::replaceInTokenVector(body_tokens, "`\"", "\"");
  StringUtils::replaceInTokenVector(body_tokens, "`\\`\"", "\\\"");

  // argument substitution
  for (std::string& actual_arg : actual_args) {
    if (actual_arg.find('`') != std::string::npos) {
      actual_arg = evaluateMacroInstance(
          actual_arg, callingFile, callingLine, SpecialInstructions::CheckLoop,
          SpecialInstructions::AsIsUndefinedMacroInstr::ComplainUndefinedMacro);
    }
    actual_arg = StringUtils::trim(actual_arg);
  }

  if ((actual_args.size() > formal_args.size() && (!m_instructions.m_mute))) {
    if (formal_args.empty() && (getFirstNonEmptyToken(body_tokens) == "(")) {
      Location loc(macroInfo->m_fileId, macroInfo->m_startLine,
                   macroInfo->m_startColumn + name.size() + 1, getId(name));
      Error err(ErrorDefinition::PP_MACRO_HAS_SPACE_BEFORE_ARGS, loc);
      addError(err);
    } else if ((!Waiver::macroArgCheck(name)) && !formal_args.empty()) {
      Location loc(callingFile->getFileId(callingLine),
                   callingFile->getLineNb(callingLine), 0, getId(name));
      Location arg(BadPathId, 0, 0,
                   registerSymbol(std::to_string(actual_args.size())));
      Location def(macroInfo->m_fileId, macroInfo->m_startLine,
                   macroInfo->m_startColumn,
                   registerSymbol(std::to_string(formal_args.size())));
      std::vector<Location> locs = {arg, def};
      Error err(ErrorDefinition::PP_TOO_MANY_ARGS_MACRO, loc, &locs);
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
                       macroInfo->m_startColumn, id);
          std::vector<Location> locs = {arg, def};
          Error err(ErrorDefinition::PP_MACRO_NO_DEFAULT_VALUE, loc, &locs);
          addError(err);
        }
        incorrectArgNb = true;
      }
    }
  }
  if (incorrectArgNb) {
    return std::make_pair(true, StrCat("`", name));
  }
  std::string body;
  for (const auto& token : body_tokens) {
    body += token;
  }
  if (!actual_args.empty() && formal_args.empty()) {
    body += "(";
    body += actual_args[0];
    body += ")";
  }
  // *** Body processing
  std::string body_short;
  // Replace \\n by \n
  bool inString = false;
  char previous = '\0';
  for (char c : body) {
    if (c == '"') {
      inString = !inString;
    }
    if ((previous == '\\') && (c == '\n') && (!inString)) {
      body_short.erase(body_short.end() - 1);
      body_short.push_back(c);
    } else {
      body_short.push_back(c);
    }
    previous = c;
  }
  // Truncate trailing carriage returns (up to 2)

  for (int32_t i = 0; i < 2; i++) {
    if (!body_short.empty()) {
      if (body_short.at(body_short.size() - 1) == '\n') {
        body_short.erase(body_short.size() - 1);
      } else {
        break;
      }
    }
  }

  // If it is a Multiline macro, insert a \n at the end

  if (body_short.find('\n') != std::string::npos) {
    body_short.push_back('\n');
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
        macroId, m_compileSourceFile, instructions,
        callingFile ? callingFile->m_compilationUnit
                    : m_includer->m_compilationUnit,
        callingFile ? callingFile->m_library : m_includer->m_library,
        callingFile ? callingFile : m_includer, callingLine, body_short,
        macroInfo, embeddedMacroCallLine - 1, embeddedMacroCallFile);
    getCompileSourceFile()->registerPP(pp);
    if (!pp->preprocess()) {
      result = MacroNotDefined;
    } else {
      std::string pp_result = pp->getPreProcessedFileContent();

      if (callingLine && callingFile && !callingFile->isMacroBody()) {
        pp_result = std::regex_replace(
            pp_result, std::regex(PP__File__Marking),
            StrCat("\"",
                   fileSystem->toPath(callingFile->getFileId(callingLine)),
                   "\""));
        pp_result = std::regex_replace(pp_result, std::regex(PP__Line__Marking),
                                       std::to_string(callingLine));
      }
      result = pp_result;
      found = true;
    }
  } else {
    result = body_short;
    found = true;
  }
  return std::make_pair(found, result);
}

MacroInfo* PreprocessFile::getMacro(std::string_view name) {
  registerSymbol(name);
  return m_compilationUnit->getMacroInfo(name);
}

bool PreprocessFile::deleteMacro(std::string_view name,
                                 std::set<PreprocessFile*>& visited) {
  /*SymbolId macroId = */ registerSymbol(name);
  if (m_debugMacro)
    std::cout << "PP CALL TO deleteMacro for " << name << std::endl;
  bool found = false;
  // Try CommandLine overrides
  // const std::map<SymbolId,std::string>& defines =
  // m_compileSourceFile->m_commandLineParser->getDefineList();
  // std::map<SymbolId,std::string>::const_iterator itMap =
  // defines.find(macroId);
  // if (itMap != defines.end())
  //  {
  //    result = (*itMap).second;
  //    found = true;
  //  }

  // Try local file scope
  if (found == false) {
    MacroStorage::iterator itr = m_macros.find(name);
    if (itr != m_macros.end()) {
      for (auto& macro : itr->second) {
        delete macro;
      }
      m_macros.erase(itr);
      m_compilationUnit->deleteMacro(name);
      found = true;
    }
  }
  // Try in included files
  if (found == false) {
    for (PreprocessFile* pFile : m_includes) {
      if (visited.insert(pFile).second) {
        bool tmp = pFile->deleteMacro(name, visited);
        if (tmp == true) {
          found = true;
          break;
        }
      }
    }
  }
  // Try in file that included this file
  if ((found == false) && (m_includer != nullptr)) {
    if (visited.insert(m_includer).second) {
      bool tmp = m_includer->deleteMacro(name, visited);
      if (tmp == true) {
        found = true;
      }
    }
  }
  return found;
}

void PreprocessFile::undefineAllMacros(std::set<PreprocessFile*>& visited) {
  if (m_debugMacro) std::cout << "PP CALL TO undefineAllMacros" << std::endl;
  for (auto& [name, macros] : m_macros) {
    for (auto& macro : macros) {
      delete macro;
    }
  }
  m_macros.clear();
  m_compilationUnit->deleteAllMacros();

  for (PreprocessFile* pFile : m_includes) {
    if (visited.find(pFile) == visited.end()) {
      visited.insert(pFile);
      pFile->undefineAllMacros(visited);
    }
  }

  if (m_includer) {
    if (visited.find(m_includer) == visited.end()) {
      visited.insert(m_includer);
      m_includer->undefineAllMacros(visited);
    }
  }
}

std::string PreprocessFile::getMacro(
    std::string_view name, std::vector<std::string>& arguments,
    PreprocessFile* callingFile, uint32_t callingLine, LoopCheck& loopChecker,
    SpecialInstructions& instructions, uint32_t embeddedMacroCallLine,
    PathId embeddedMacroCallFile) {
  SymbolId macroId = registerSymbol(name);
  if (m_debugMacro) {
    std::cout << "PP CALL TO getMacro for " << name << "\n";
    for (const auto& arg : arguments) {
      std::cout << "PP ARG: " << arg << "\n";
    }
    instructions.print();
  }
  std::string result;
  bool found = false;
  // Try CommandLine overrides
  const auto& defines =
      m_compileSourceFile->m_commandLineParser->getDefineList();
  auto itMap = defines.find(macroId);
  if (itMap != defines.end()) {
    result = (*itMap).second;
    found = true;
  }

  // Try local file scope
  if (found == false) {
    MacroInfo* info = m_compilationUnit->getMacroInfo(name);
    if (instructions.m_evaluate == SpecialInstructions::Evaluate) {
      if (info) {
        std::pair<bool, std::string> evalResult = evaluateMacro_(
            name, arguments, callingFile, callingLine, loopChecker, info,
            instructions, embeddedMacroCallLine, embeddedMacroCallFile);
        found = evalResult.first;
        result = evalResult.second;
        result = std::regex_replace(result, std::regex("``"), "");
      }
    } else {
      if (info) {
        found = true;
        result.clear();
      }
    }
  }
  if (found == false) {
    if (instructions.m_as_is_undefined_macro ==
        SpecialInstructions::AsIsUndefinedMacro) {
      return StrCat("`", name);
    } else {
      return MacroNotDefined;
    }
  } else {
    return result;
  }
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

std::string PreprocessFile::getPreProcessedFileContent() {
  FileSystem* const fileSystem = FileSystem::getInstance();
  // If File is empty (Only CR) return an empty string
  bool nonEmpty = false;
  uint32_t pp_result_size = m_result.size();
  for (uint32_t i = 0; i < pp_result_size; i++) {
    if ((m_result[i] != '\n') && (m_result[i] != ' ')) {
      nonEmpty = true;
      break;
    }
  }
  if (!nonEmpty) m_result.clear();
  if (m_debugPPResult) {
    std::string objName =
        m_macroBody.empty()
            ? std::string("file ").append(fileSystem->toPath(m_fileId))
            : std::string("macro ").append(m_macroBody);
    std::cout << "PP RESULT for " << objName
              << " : \nvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv\n"
              << m_result << "\n^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n"
              << std::endl;
  }
  return m_result;
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
  CommandLineParser* clp = getCompileSourceFile()->getCommandLineParser();
  if (clp->parseOnly() || clp->lowMem() || clp->link()) return;
  if (m_macroBody.empty()) {
    if (!m_usingCachedVersion) {
      PPCache cache(this);
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
