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
 * File:   ParseFile.cpp
 * Author: alain
 *
 * Created on February 24, 2017, 10:03 PM
 */

#include "Surelog/SourceCompile/ParseFile.h"

#include <antlr4-runtime.h>
#include <parser/SV3_1aLexer.h>
#include <parser/SV3_1aParser.h>

#include <cstdint>
#include <iostream>
#include <memory>
#include <string>
#include <string_view>

#include "Surelog/Cache/ParseCache.h"
#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Common/PathId.h"
#include "Surelog/Common/Session.h"
#include "Surelog/Common/SymbolId.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/ErrorReporting/Error.h"
#include "Surelog/ErrorReporting/ErrorContainer.h"
#include "Surelog/ErrorReporting/ErrorDefinition.h"
#include "Surelog/ErrorReporting/Location.h"
#include "Surelog/Package/Precompiled.h"
#include "Surelog/SourceCompile/AntlrParserErrorListener.h"
#include "Surelog/SourceCompile/AntlrParserHandler.h"
#include "Surelog/SourceCompile/CompileSourceFile.h"
#include "Surelog/SourceCompile/IncludeFileInfo.h"
#include "Surelog/SourceCompile/SV3_1aParserTreeListener.h"
#include "Surelog/SourceCompile/SV3_1aTreeShapeListener.h"
#include "Surelog/SourceCompile/SymbolTable.h"
#include "Surelog/Utils/StringUtils.h"
#include "Surelog/Utils/Timer.h"

namespace SURELOG {
ParseFile::ParseFile(Session* session, PathId fileId)
    : m_session(session),
      m_fileId(fileId),
      m_compileSourceFile(nullptr),
      m_compilationUnit(nullptr),
      m_library(nullptr),
      m_antlrParserHandler(nullptr),
      m_listener(nullptr),
      m_usingCachedVersion(false),
      m_keepParserHandler(false),
      m_fileContent(nullptr),
      debug_AstModel(false),
      m_parent(nullptr),
      m_offsetLine(0) {
  debug_AstModel = false;
}

ParseFile::ParseFile(Session* session, PathId fileId, CompileSourceFile* csf,
                     CompilationUnit* compilationUnit, Library* library,
                     PathId ppFileId, bool keepParserHandler)
    : m_session(session),
      m_fileId(fileId),
      m_ppFileId(ppFileId),
      m_compileSourceFile(csf),
      m_compilationUnit(compilationUnit),
      m_library(library),
      m_antlrParserHandler(nullptr),
      m_listener(nullptr),
      m_usingCachedVersion(false),
      m_keepParserHandler(keepParserHandler),
      m_fileContent(nullptr),
      debug_AstModel(false),
      m_parent(nullptr),
      m_offsetLine(0) {
  debug_AstModel = m_session->getCommandLineParser()->getDebugAstModel();
}

ParseFile::ParseFile(Session* session, CompileSourceFile* compileSourceFile,
                     ParseFile* parent, PathId chunkFileId, uint32_t offsetLine)
    : m_session(session),
      m_fileId(parent->m_fileId),
      m_ppFileId(chunkFileId),
      m_compileSourceFile(compileSourceFile),
      m_compilationUnit(parent->m_compilationUnit),
      m_library(parent->m_library),
      m_antlrParserHandler(nullptr),
      m_listener(nullptr),
      m_usingCachedVersion(false),
      m_keepParserHandler(parent->m_keepParserHandler),
      m_fileContent(parent->m_fileContent),
      debug_AstModel(false),
      m_parent(parent),
      m_offsetLine(offsetLine) {
  parent->m_children.emplace_back(this);
}

ParseFile::ParseFile(Session* session, std::string_view text,
                     CompileSourceFile* csf, CompilationUnit* compilationUnit,
                     Library* library)
    : m_session(session),
      m_compileSourceFile(csf),
      m_compilationUnit(compilationUnit),
      m_library(library),
      m_antlrParserHandler(nullptr),
      m_listener(nullptr),
      m_usingCachedVersion(false),
      m_keepParserHandler(false),
      m_fileContent(nullptr),
      debug_AstModel(false),
      m_parent(nullptr),
      m_offsetLine(0),
      m_sourceText(text) {
  debug_AstModel = m_session->getCommandLineParser()->getDebugAstModel();
}

ParseFile::~ParseFile() {
  if (!m_keepParserHandler) delete m_antlrParserHandler;
  delete m_listener;
}

SymbolId ParseFile::registerSymbol(std::string_view symbol) {
  return m_session->getSymbolTable()->registerSymbol(symbol);
}

SymbolId ParseFile::getId(std::string_view symbol) const {
  return m_session->getSymbolTable()->getId(symbol);
}

std::string_view ParseFile::getSymbol(SymbolId id) const {
  return m_session->getSymbolTable()->getSymbol(id);
}

void ParseFile::addError(Error& error) {
  m_session->getErrorContainer()->addError(error);
}

PathId ParseFile::getFileId(uint32_t line) {
  if ((line == 0) || !getCompileSourceFile()) return m_fileId;

  PreprocessFile* pp = getCompileSourceFile()->getPreprocessor();
  if (!pp) return BadPathId;

  const auto& infos = pp->getIncludeFileInfo();
  if (infos.empty()) return m_fileId;

  if (m_locationCache.empty()) buildLocationCache();

  if (line < m_locationCache.size()) {
    return m_locationCache[line][0].m_fileId;
  }

  SymbolId fileId = registerSymbol("FILE CACHE OUT OF BOUND");
  Location ppfile(fileId);
  Error err(ErrorDefinition::PA_INTERNAL_WARNING, ppfile);
  addError(err);

  return m_fileId;
}

uint32_t ParseFile::getLineNb(uint32_t line) {
  if (!getCompileSourceFile()) return line;

  PreprocessFile* pp = getCompileSourceFile()->getPreprocessor();
  if (!pp) return 0;

  auto& infos = pp->getIncludeFileInfo();
  if (infos.empty()) return line;

  if (m_locationCache.empty()) buildLocationCache();

  if (line < m_locationCache.size()) {
    return m_locationCache[line][0].m_line;
  }

  SymbolId fileId = registerSymbol("LINE CACHE OUT OF BOUND");
  Location ppfile(fileId);
  Error err(ErrorDefinition::PA_INTERNAL_WARNING, ppfile);
  addError(err);

  return line;
}

void ParseFile::printLocationCache() const {
#ifdef _WIN32
  FileSystem* const fileSystem = m_session->getFileSystem();
  // std::string filepath =
  //    fileSystem->toPlatformAbsPath(m_fileId).string() + ".log";
  // std::ofstream strm(filepath);
  std::ostream& strm = std::cout;

  uint32_t index = 0;
  strm << "File: " << PathIdPP(m_fileId, fileSystem) << std::endl;
  for (const auto& entry1 : m_locationCache) {
    for (const auto& entry2 : entry1) {
      strm << index << ": " << entry2.m_column << ", "
           << PathIdPP(entry2.m_fileId, fileSystem) << ", " << entry2.m_line
           << ", " << entry2.m_offset << ", " << entry2.m_hint << std::endl;
    }
    strm << std::endl;
    ++index;
  }
  strm << std::endl << std::endl;
  strm << std::flush;
  // strm.close();
#endif
}

void ParseFile::buildLocationCache_recurse(uint32_t index) {
  auto const& infos =
      getCompileSourceFile()->getPreprocessor()->getIncludeFileInfo();
  const IncludeFileInfo& oifi = infos[index];
  const IncludeFileInfo& cifi = infos[oifi.m_indexOpposite];

  uint32_t sourceLine = oifi.m_sourceLine;
  uint32_t targetLine = 1;
  PathId targetFileId;

  if (oifi.m_context == IncludeFileInfo::Context::Include) {
    targetFileId = oifi.m_sectionFileId;
    while (sourceLine < oifi.m_sourceLine) {
      m_locationCache[sourceLine++].emplace_back(1, targetFileId, targetLine++,
                                                 0, index);
    }
    m_locationCache[sourceLine].emplace_back(1, targetFileId, targetLine, 0,
                                             index);
    if (oifi.m_sourceColumn > 1) {
      m_locationCache[sourceLine].emplace_back(
          oifi.m_sourceColumn, targetFileId, targetLine, 0, index);
    }
  } else if (oifi.m_context == IncludeFileInfo::Context::Macro) {
    targetLine = oifi.m_macroDefinition->m_startLine;
    targetFileId = oifi.m_macroDefinition->m_fileId;
    m_locationCache[sourceLine].emplace_back(
        oifi.m_sourceColumn, targetFileId, targetLine,
        oifi.m_sourceColumn - oifi.m_macroDefinition->m_bodyStartColumn, index);
  }

  int32_t pio = -1;
  for (int32_t i = index + 1; i < oifi.m_indexOpposite; ++i) {
    const IncludeFileInfo& ioifi = infos[i];
    if (ioifi.m_action != IncludeFileInfo::Action::Push) continue;

    const IncludeFileInfo& icifi = infos[ioifi.m_indexOpposite];

    while (sourceLine < ioifi.m_sourceLine) {
      m_locationCache[++sourceLine].emplace_back(1, targetFileId, ++targetLine,
                                                 0, index);
    }

    buildLocationCache_recurse(i);

    targetLine += (icifi.m_symbolLine - ioifi.m_symbolLine);

    if (ioifi.m_context == IncludeFileInfo::Context::Include) {
      if (icifi.m_sourceColumn > 1) {
        // Included file doesn't have newline at the end of the file!
        m_locationCache[sourceLine].emplace_back(
            icifi.m_sourceColumn, targetFileId, targetLine,
            icifi.m_sourceColumn - icifi.m_symbolColumn, index);
      }
    } else if (ioifi.m_context == IncludeFileInfo::Context::Macro) {
      m_locationCache[icifi.m_sourceLine].emplace_back(
          icifi.m_sourceColumn, targetFileId, targetLine,
          icifi.m_sourceColumn - icifi.m_symbolColumn, index);
    }

    pio = i;
    i = ioifi.m_indexOpposite;
    sourceLine = icifi.m_sourceLine;
  }

  if ((oifi.m_context == IncludeFileInfo::Context::Include) && (pio > 0)) {
    const IncludeFileInfo& pioifi = infos[pio];
    const IncludeFileInfo& picifi = infos[pioifi.m_indexOpposite];

    if ((picifi.m_context == IncludeFileInfo::Context::Include) &&
        (picifi.m_sourceColumn > 1)) {
      // Last included file doesn't have a newline at the end of the file!
      m_locationCache[sourceLine].emplace_back(
          picifi.m_sourceColumn, targetFileId, targetLine - 1,
          picifi.m_sourceColumn - picifi.m_symbolColumn, index);
    }

    if (picifi.m_sourceLine < cifi.m_sourceLine) {
      ++sourceLine;
      ++targetLine;
    }
  }

  while (sourceLine <= cifi.m_sourceLine) {
    if (m_locationCache[sourceLine].empty()) {
      m_locationCache[sourceLine].emplace_back(1, targetFileId, targetLine, 0,
                                               index);
    }
    ++sourceLine;
    ++targetLine;
  }

  if (oifi.m_context == IncludeFileInfo::Context::Macro) {
    m_locationCache[cifi.m_sourceLine].emplace_back(
        cifi.m_sourceColumn, targetFileId, targetLine - 1,
        cifi.m_sourceColumn - cifi.m_sectionColumn, index);
  }
}

void ParseFile::buildLocationCache() {
  PreprocessFile* pp = getCompileSourceFile()->getPreprocessor();
  if (!pp) return;

  auto& infos = pp->getIncludeFileInfo();
  if (infos.empty()) return;

  m_locationCache.clear();
  m_locationCache.resize(pp->getLineCount() + 10);
  m_locationCache[0].emplace_back(0, m_fileId, 0, 0, -1);
  buildLocationCache_recurse(0);

  uint32_t sourceLine = infos.back().m_sourceLine + 1;
  uint32_t targetLine = m_locationCache[sourceLine - 1].back().m_line + 1;
  while (sourceLine < m_locationCache.size()) {
    m_locationCache[sourceLine++].emplace_back(1, m_fileId, targetLine++, 0, 0);
  }
  // printLocationCache();
}

ParseFile::MapLocationResult ParseFile::mapLocations(uint32_t sl, uint16_t sc,
                                                     uint32_t el, uint16_t ec) {
  MapLocationResult result = {m_fileId, sl, sc, m_fileId, el, ec};
  if (!getCompileSourceFile()) return result;

  PreprocessFile* pp = getCompileSourceFile()->getPreprocessor();
  if (!pp) return result;

  const auto& infos = pp->getIncludeFileInfo();
  if (infos.empty()) return result;

  if (m_locationCache.empty()) buildLocationCache();
  if (m_locationCache.empty()) return result;

  const location_cache_entry_t& sentry = m_locationCache[sl];
  const location_cache_entry_t& eentry = m_locationCache[el];

  if ((sentry.size() == 1) && (eentry.size() == 1)) {
    result.m_startFileId = sentry[0].m_fileId;
    result.m_startLine = sentry[0].m_line;
    result.m_startColumn = sc - sentry[0].m_offset;
    result.m_endFileId = eentry[0].m_fileId;
    result.m_endLine = eentry[0].m_line;
    result.m_endColumn = ec - eentry[0].m_offset;
    return result;
  }

  int32_t si = -1;
  if ((sl > 0) && (sl < m_locationCache.size())) {
    for (uint32_t i = 0, ni = sentry.size(); i < ni; ++i) {
      const location_cache_entry_t::value_type& item = sentry[i];

      if (item.m_column <= sc) {
        si = i;
      } else {
        break;
      }
    }
  }

  int32_t ei = -1;
  if ((el > 0) && (el < m_locationCache.size())) {
    for (uint32_t i = 0, ni = eentry.size(); i < ni; ++i) {
      const location_cache_entry_t::value_type& item = eentry[i];

      if (item.m_column < ec) {
        ei = i;
      } else {
        break;
      }
    }
  }

  if ((si >= 0) && (ei >= 0) && (sentry[si].m_hint != eentry[ei].m_hint) &&
      ((si + 1) == ei) && (eentry[ei].m_column == ec)) {
    ei = si;
  }

  if ((si >= 0) && (ei >= 0) && (sentry[si].m_hint != eentry[ei].m_hint)) {
    bool found = false;
    for (int32_t i = si; i >= 0 && !found; --i) {
      const location_cache_entry_t::value_type& sitem = sentry[i];

      for (int32_t j = ei, nj = eentry.size(); j < nj && !found; ++j) {
        const location_cache_entry_t::value_type& eitem = eentry[j];

        if (ec >= eitem.m_column) {
          if (sitem.m_hint == eitem.m_hint) {
            si = i;
            ei = j;
            found = true;
          }
        } else {
          break;
        }
      }
    }
  }

  if (si >= 0) {
    const location_cache_entry_t::value_type& item = sentry[si];
    result.m_startFileId = item.m_fileId;
    result.m_startLine = item.m_line;
    result.m_startColumn = sc - item.m_offset;
  }

  if (ei >= 0) {
    const location_cache_entry_t::value_type& item = eentry[ei];
    result.m_endFileId = item.m_fileId;
    result.m_endLine = item.m_line;
    result.m_endColumn = ec - item.m_offset;
  }

  return result;
}

bool ParseFile::parseOneFile_(PathId fileId, uint32_t lineOffset) {
  SymbolTable* const symbols = m_session->getSymbolTable();
  FileSystem* const fileSystem = m_session->getFileSystem();
  CommandLineParser* const clp = m_session->getCommandLineParser();
  PreprocessFile* pp = getCompileSourceFile()->getPreprocessor();
  Timer tmr;
  m_antlrParserHandler = new AntlrParserHandler();
  m_antlrParserHandler->m_clearAntlrCache = clp->lowMem();
  if (m_sourceText.empty()) {
    std::istream& stream = fileSystem->openForRead(fileId);
    if (!stream.good()) {
      fileSystem->close(stream);
      Location ppfile(fileId);
      Error err(ErrorDefinition::PA_CANNOT_OPEN_FILE, ppfile);
      addError(err);
      return false;
    }
    m_antlrParserHandler->m_inputStream = new antlr4::ANTLRInputStream(stream);
    fileSystem->close(stream);
  } else {
    m_antlrParserHandler->m_inputStream =
        new antlr4::ANTLRInputStream(m_sourceText);
  }

  m_antlrParserHandler->m_errorListener =
      new AntlrParserErrorListener(m_session, this, false, lineOffset, fileId);
  m_antlrParserHandler->m_lexer =
      new SV3_1aLexer(m_antlrParserHandler->m_inputStream);
  VerilogVersion version = VerilogVersion::SystemVerilog;
  if (pp) version = pp->getVerilogVersion();
  if (version != VerilogVersion::NoVersion) {
    switch (version) {
      case VerilogVersion::NoVersion:
        break;
      case VerilogVersion::Verilog1995:
        m_antlrParserHandler->m_lexer->sverilog = false;
        break;
      case VerilogVersion::Verilog2001:
        m_antlrParserHandler->m_lexer->sverilog = false;
        break;
      case VerilogVersion::Verilog2005:
        m_antlrParserHandler->m_lexer->sverilog = false;
        break;
      case VerilogVersion::SVerilog2005:
        m_antlrParserHandler->m_lexer->sverilog = true;
        break;
      case VerilogVersion::Verilog2009:
        m_antlrParserHandler->m_lexer->sverilog = true;
        break;
      case VerilogVersion::SystemVerilog:
        m_antlrParserHandler->m_lexer->sverilog = true;
        break;
    }
  } else {
    std::string_view type = std::get<1>(fileSystem->getType(fileId, symbols));
    m_antlrParserHandler->m_lexer->sverilog =
        (type == ".sv") || clp->fullSVMode() || clp->isSVFile(fileId);
  }

  m_antlrParserHandler->m_lexer->removeErrorListeners();
  m_antlrParserHandler->m_lexer->addErrorListener(
      m_antlrParserHandler->m_errorListener);
  m_antlrParserHandler->m_tokens =
      new antlr4::CommonTokenStream(m_antlrParserHandler->m_lexer);
  m_antlrParserHandler->m_tokens->fill();

  if (clp->profile()) {
    // m_profileInfo += "Tokenizer: " + std::to_string (tmr.elapsed_rounded
    // ())
    // + " " + fileName + "\n";
    tmr.reset();
  }

  // Simulator options showed up in Antlr when also ANTLRCPP_VERSION was
  // first defined, so testing with ifdef helps us to decide to use options.
#ifdef ANTLRCPP_VERSION
  antlr4::atn::ParserATNSimulatorOptions options;
  options.setPredictionContextMergeCacheOptions(
      antlr4::atn::PredictionContextMergeCacheOptions()
          .setMaxSize(10000)
          .setClearEveryN(100));

  m_antlrParserHandler->m_parser =
      new SV3_1aParser(m_antlrParserHandler->m_tokens, options);
#else
  m_antlrParserHandler->m_parser =
      new SV3_1aParser(m_antlrParserHandler->m_tokens);
#endif

  if (clp->profile()) {
    m_antlrParserHandler->m_parser->setProfile(true);
  }
  m_antlrParserHandler->m_parser
      ->getInterpreter<antlr4::atn::ParserATNSimulator>()
      ->setPredictionMode(antlr4::atn::PredictionMode::SLL);
  m_antlrParserHandler->m_parser->removeErrorListeners();
  m_antlrParserHandler->m_parser->setErrorHandler(
      std::make_shared<antlr4::BailErrorStrategy>());

  try {
    m_antlrParserHandler->m_tree =
        m_antlrParserHandler->m_parser->top_level_rule();

    if (clp->profile()) {
      StrAppend(&m_profileInfo,
                "SLL Parsing: ", StringUtils::to_string(tmr.elapsed_rounded()),
                "s ", fileSystem->toPath(fileId), "\n");
      tmr.reset();
      profileParser();
    }
  } catch (antlr4::ParseCancellationException&) {
    m_antlrParserHandler->m_tokens->reset();
    m_antlrParserHandler->m_parser->reset();
    m_antlrParserHandler->m_parser->removeErrorListeners();
    if (clp->profile()) {
      m_antlrParserHandler->m_parser->setProfile(true);
    }
    m_antlrParserHandler->m_parser->setErrorHandler(
        std::make_shared<antlr4::DefaultErrorStrategy>());
    m_antlrParserHandler->m_parser->addErrorListener(
        m_antlrParserHandler->m_errorListener);
    m_antlrParserHandler->m_parser
        ->getInterpreter<antlr4::atn::ParserATNSimulator>()
        ->setPredictionMode(antlr4::atn::PredictionMode::LL);
    m_antlrParserHandler->m_tree =
        m_antlrParserHandler->m_parser->top_level_rule();

    if (clp->profile()) {
      StrAppend(&m_profileInfo,
                "LL  Parsing: ", StringUtils::to_string(tmr.elapsed_rounded()),
                "s ", fileSystem->toPath(fileId), "\n");
      tmr.reset();
      profileParser();
    }
  }
  /* Failed attempt to minimize memory usage:
     m_antlrParserHandler->m_parser->getInterpreter<antlr4::atn::ParserATNSimulator>()->clearDFA();
     SV3_1aParser::_sharedContextCache.clear();
  */
  return true;
}

void ParseFile::profileParser() {
  // Core dumps
  /*
  for (auto iterator =
  m_antlrParserHandler->m_parser->getParseInfo().getDecisionInfo().begin();
       iterator !=
  m_antlrParserHandler->m_parser->getParseInfo().getDecisionInfo().end();
  iterator++) { antlr4::atn::DecisionInfo& decisionInfo = *iterator;
    antlr4::atn::DecisionState* ds =
        m_antlrParserHandler->m_parser->getATN().getDecisionState(decisionInfo.decision);
    std::string rule =
  m_antlrParserHandler->m_parser->getRuleNames()[ds->ruleIndex]; if
  (decisionInfo.timeInPrediction > 0) { std::cout << std::left << std::setw(35)
  << std::setfill(' ') << rule; std::cout << std::left << std::setw(15) <<
  std::setfill(' ')
                << decisionInfo.timeInPrediction;
      std::cout << std::left << std::setw(15) << std::setfill(' ')
                << decisionInfo.invocations;
      std::cout << std::left << std::setw(15) << std::setfill(' ')
                << decisionInfo.SLL_TotalLook;
      std::cout << std::left << std::setw(15) << std::setfill(' ')
                << decisionInfo.SLL_MaxLook;
      std::cout << std::left << std::setw(15) << std::setfill(' ')
                << decisionInfo.ambiguities.size();
      std::cout << std::left << std::setw(15) << std::setfill(' ')
                << decisionInfo.errors.size();
      std::cout << std::endl;
    }
  }
  */
}

std::string ParseFile::getProfileInfo() const {
  std::string profile;
  profile = m_profileInfo;
  for (const ParseFile* child : m_children) {
    profile += child->m_profileInfo;
  }
  return profile;
}

bool ParseFile::parse() {
  FileSystem* const fileSystem = m_session->getFileSystem();
  CommandLineParser* const clp = m_session->getCommandLineParser();

  if (m_children.empty()) {
    ParseCache cache(m_session, this);

    if (cache.restore()) {
      m_usingCachedVersion = true;
      if (debug_AstModel && m_fileId) {
        m_fileContent->printTree(std::cout);
      }
      if (clp->debugCache()) {
        std::cout << "PARSER CACHE USED FOR: "
                  << fileSystem->toPath(getFileId(0)) << std::endl;
      }
      return true;
    }
  } else {
    bool ok = true;
    for (ParseFile* child : m_children) {
      ParseCache cache(m_session, child);

      if (cache.restore()) {
        child->m_fileContent->setParent(m_fileContent);
        m_usingCachedVersion = true;
        if (debug_AstModel && m_fileId) {
          child->m_fileContent->printTree(std::cout);
        }
      } else {
        ok = false;
      }
    }
    if (ok) {
      if (clp->debugCache()) {
        std::cout << "PARSER CACHE USED FOR: "
                  << fileSystem->toPath(getFileId(0)) << std::endl;
      }
      return true;
    }
  }

  // This is not a parent Parser object
  if (m_children.empty()) {
    // std::cout << std::endl << "Parsing " << getSymbol(m_ppFileId) << "
    // Line: " << m_offsetLine << std::endl << std::flush;

    parseOneFile_(m_ppFileId, m_offsetLine);

    // m_listener = new SV3_1aTreeShapeListener (this,
    // m_antlrParserHandler->m_tokens, m_offsetLine);
    // tree::ParseTreeWalker::DEFAULT.walk (m_listener,
    // m_antlrParserHandler->m_tree); std::cout << std::endl << "End Parsing "
    // << getSymbol(m_ppFileId) << " Line: " << m_offsetLine << std::endl <<
    // std::flush;
  }

  // This is either a parent Parser object of this Parser object has no parent
  if (!m_children.empty() || (m_parent == nullptr)) {
    if ((m_parent == nullptr) && (m_children.empty())) {
      Timer tmr;

      if (clp->parseTree()) {
        FileContent* const ppFileContent =
            getCompileSourceFile()->getPreprocessor()->getFileContent();
        m_listener = new SV3_1aParserTreeListener(
            m_session, this, m_antlrParserHandler->m_tokens, m_offsetLine,
            ppFileContent);
      } else {
        m_listener = new SV3_1aTreeShapeListener(
            m_session, this, m_antlrParserHandler->m_tokens, m_offsetLine);
      }

      antlr4::tree::ParseTreeWalker::DEFAULT.walk(m_listener,
                                                  m_antlrParserHandler->m_tree);

      if (!m_fileContent->validate()) {
        Location ppfile(BadSymbolId);
        Error err(ErrorDefinition::PA_INVALID_VOBJECT_LOCATION, ppfile);
        addError(err);
      }

      if (debug_AstModel && m_fileId) {
        m_fileContent->printTree(std::cout);
      }

      if (clp->profile()) {
        // m_profileInfo += "AST Walking: " + std::to_string
        // (tmr.elapsed_rounded ()) + "\n";
        tmr.reset();
      }

      ParseCache cache(m_session, this);
      if (clp->link()) return true;
      if (!cache.save()) {
        return false;
      }

      if (clp->profile()) {
        m_profileInfo +=
            "Cache saving: " + std::to_string(tmr.elapsed_rounded()) + "s\n";
        std::cout << "Cache saving: " + std::to_string(tmr.elapsed_rounded()) +
                         "s\n"
                  << std::flush;
        tmr.reset();
      }
    }

    if (!m_children.empty()) {
      for (ParseFile* child : m_children) {
        if (child->m_antlrParserHandler) {
          // Only visit the chunks that got re-parsed
          // TODO: Incrementally regenerate the FileContent
          child->m_fileContent->setParent(m_fileContent);
          if (clp->parseTree()) {
            FileContent* const ppFileContent = child->getCompileSourceFile()
                                                   ->getPreprocessor()
                                                   ->getFileContent();
            child->m_listener = new SV3_1aParserTreeListener(
                m_session, child, child->m_antlrParserHandler->m_tokens,
                child->m_offsetLine, ppFileContent);
          } else {
            child->m_listener = new SV3_1aTreeShapeListener(
                m_session, child, child->m_antlrParserHandler->m_tokens,
                child->m_offsetLine);
          }

          Timer tmr;
          antlr4::tree::ParseTreeWalker::DEFAULT.walk(
              child->m_listener, child->m_antlrParserHandler->m_tree);

          if (clp->profile()) {
            // m_profileInfo += "For file " + getSymbol
            // (child->m_ppFileId) + ", AST Walking took" +
            // std::to_string (tmr.elapsed_rounded ()) + "\n";
            tmr.reset();
          }

          if (debug_AstModel && m_fileId) {
            child->m_fileContent->printTree(std::cout);
          }

          ParseCache cache(m_session, child);
          if (clp->link()) return true;
          if (!cache.save()) {
            return false;
          }
        }
      }
    }
  }
  return true;
}
}  // namespace SURELOG
