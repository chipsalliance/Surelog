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

#include <Surelog/Cache/ParseCache.h>
#include <Surelog/CommandLine/CommandLineParser.h>
#include <Surelog/Common/FileSystem.h>
#include <Surelog/Design/FileContent.h>
#include <Surelog/ErrorReporting/ErrorContainer.h>
#include <Surelog/Package/Precompiled.h>
#include <Surelog/SourceCompile/AntlrParserErrorListener.h>
#include <Surelog/SourceCompile/AntlrParserHandler.h>
#include <Surelog/SourceCompile/CompileSourceFile.h>
#include <Surelog/SourceCompile/ParseFile.h>
#include <Surelog/SourceCompile/SV3_1aTreeShapeListener.h>
#include <Surelog/SourceCompile/SymbolTable.h>
#include <Surelog/Utils/StringUtils.h>
#include <Surelog/Utils/Timer.h>
#include <antlr4-runtime.h>
#include <parser/SV3_1aLexer.h>
#include <parser/SV3_1aParser.h>

namespace SURELOG {
ParseFile::ParseFile(PathId fileId, SymbolTable* symbolTable,
                     ErrorContainer* errors)
    : m_fileId(fileId),
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
      m_offsetLine(0),
      m_symbolTable(symbolTable),
      m_errors(errors) {
  debug_AstModel = false;
}

ParseFile::ParseFile(PathId fileId, CompileSourceFile* csf,
                     CompilationUnit* compilationUnit, Library* library,
                     PathId ppFileId, bool keepParserHandler)
    : m_fileId(fileId),
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
      m_offsetLine(0),
      m_symbolTable(nullptr),
      m_errors(nullptr) {
  debug_AstModel =
      m_compileSourceFile->getCommandLineParser()->getDebugAstModel();
}

ParseFile::ParseFile(CompileSourceFile* compileSourceFile, ParseFile* parent,
                     PathId chunkFileId, uint32_t offsetLine)
    : m_fileId(parent->m_fileId),
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
      m_offsetLine(offsetLine),
      m_symbolTable(nullptr),
      m_errors(nullptr) {
  parent->m_children.push_back(this);
}

ParseFile::ParseFile(std::string_view text, CompileSourceFile* csf,
                     CompilationUnit* compilationUnit, Library* library)
    : m_compileSourceFile(csf),
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
      m_symbolTable(csf->getSymbolTable()),
      m_errors(csf->getErrorContainer()),
      m_sourceText(text) {
  debug_AstModel =
      m_compileSourceFile->getCommandLineParser()->getDebugAstModel();
}

ParseFile::~ParseFile() {
  if (!m_keepParserHandler) delete m_antlrParserHandler;
  delete m_listener;
}

SymbolTable* ParseFile::getSymbolTable() {
  return m_symbolTable ? m_symbolTable : m_compileSourceFile->getSymbolTable();
}

ErrorContainer* ParseFile::getErrorContainer() {
  return m_errors ? m_errors : m_compileSourceFile->getErrorContainer();
}

SymbolId ParseFile::registerSymbol(std::string_view symbol) {
  return getCompileSourceFile()->getSymbolTable()->registerSymbol(symbol);
}

SymbolId ParseFile::getId(std::string_view symbol) const {
  return getCompileSourceFile()->getSymbolTable()->getId(symbol);
}

std::string_view ParseFile::getSymbol(SymbolId id) const {
  return getCompileSourceFile()->getSymbolTable()->getSymbol(id);
}

void ParseFile::addError(Error& error) {
  getCompileSourceFile()->getErrorContainer()->addError(error);
}

void ParseFile::buildLineInfoCache_() {
  PreprocessFile* pp = getCompileSourceFile()->getPreprocessor();
  if (!pp) return;
  auto const& infos = pp->getIncludeFileInfo();
  if (!infos.empty()) {
    fileInfoCache.resize(pp->getSumLineCount() + 10);
    lineInfoCache.resize(pp->getSumLineCount() + 10);
    lineInfoCache[0] = 1;
    fileInfoCache[0] = m_fileId;
    for (uint32_t lineItr = 1; lineItr < pp->getSumLineCount() + 10;
         lineItr++) {
      fileInfoCache[lineItr] = m_fileId;
      lineInfoCache[lineItr] = lineItr;
      bool inRange = false;
      uint32_t indexOpeningRange = 0;
      uint32_t index = infos.size() - 1;
      while (1) {
        if ((lineItr >= infos[index].m_originalStartLine) &&
            (infos[index].m_action == IncludeFileInfo::Action::POP)) {
          fileInfoCache[lineItr] = infos[index].m_sectionFileId;
          uint32_t l = infos[index].m_sectionStartLine +
                       (lineItr - infos[index].m_originalStartLine);
          lineInfoCache[lineItr] = l;
          break;
        }
        if (infos[index].m_action == IncludeFileInfo::Action::POP) {
          if (!inRange) {
            inRange = true;
            indexOpeningRange = infos[index].m_indexOpening;
          }
        } else {
          if (inRange) {
            if (index == indexOpeningRange) inRange = false;
          }
        }
        if ((lineItr >= infos[index].m_originalStartLine) &&
            (infos[index].m_action == IncludeFileInfo::Action::PUSH) &&
            (infos[index].m_indexClosing > -1) &&
            (lineItr <
             infos[infos[index].m_indexClosing].m_originalStartLine)) {
          fileInfoCache[lineItr] = infos[index].m_sectionFileId;
          uint32_t l = infos[index].m_sectionStartLine +
                       (lineItr - infos[index].m_originalStartLine);
          lineInfoCache[lineItr] = l;
          break;
        }
        if (index == 0) break;
        index--;
      }
    }
  }
}

PathId ParseFile::getFileId(uint32_t line) {
  if (!getCompileSourceFile()) {
    return m_fileId;
  }
  PreprocessFile* pp = getCompileSourceFile()->getPreprocessor();
  if (!pp) return BadPathId;
  auto& infos = pp->getIncludeFileInfo();
  if (!infos.empty()) {
    if (!fileInfoCache.empty()) {
      if (line > fileInfoCache.size()) {
        SymbolId fileId = registerSymbol("CACHE OUT OF BOUND");
        Location ppfile(fileId);
        Error err(ErrorDefinition::PA_INTERNAL_WARNING, ppfile);
        addError(err);
        return m_fileId;
      }
      return fileInfoCache[line];
    }
    buildLineInfoCache_();
    if (line > fileInfoCache.size()) {
      SymbolId fileId = registerSymbol("CACHE OUT OF BOUND");
      Location ppfile(fileId);
      Error err(ErrorDefinition::PA_INTERNAL_WARNING, ppfile);
      addError(err);
      return m_fileId;
    }
    return fileInfoCache[line];
  } else {
    return m_fileId;
  }
}

uint32_t ParseFile::getLineNb(uint32_t line) {
  if (!getCompileSourceFile()) return line;
  PreprocessFile* pp = getCompileSourceFile()->getPreprocessor();
  if (!pp) return 0;
  auto& infos = pp->getIncludeFileInfo();
  if (!infos.empty()) {
    if (!lineInfoCache.empty()) {
      if (line > lineInfoCache.size()) {
        SymbolId fileId = registerSymbol("CACHE OUT OF BOUND");
        Location ppfile(fileId);
        Error err(ErrorDefinition::PA_INTERNAL_WARNING, ppfile);
        addError(err);
        return line;
      }
      return lineInfoCache[line];
    }
    buildLineInfoCache_();
    if (line > lineInfoCache.size()) {
      SymbolId fileId = registerSymbol("CACHE OUT OF BOUND");
      Location ppfile(fileId);
      Error err(ErrorDefinition::PA_INTERNAL_WARNING, ppfile);
      addError(err);
      return line;
    }
    return lineInfoCache[line];
  } else {
    return line;
  }
}

bool ParseFile::parseOneFile_(PathId fileId, uint32_t lineOffset) {
  FileSystem* const fileSystem = FileSystem::getInstance();
  CommandLineParser* clp = getCompileSourceFile()->getCommandLineParser();
  PreprocessFile* pp = getCompileSourceFile()->getPreprocessor();
  Timer tmr;
  m_antlrParserHandler = new AntlrParserHandler();
  m_antlrParserHandler->m_clearAntlrCache = clp->lowMem();
  if (m_sourceText.empty()) {
    std::istream& stream = fileSystem->openForRead(fileId);
    if (!stream.good()) {
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
      new AntlrParserErrorListener(this, false, lineOffset, fileId);
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
    std::string_view type = std::get<1>(
        fileSystem->getType(fileId, getCompileSourceFile()->getSymbolTable()));
    m_antlrParserHandler->m_lexer->sverilog =
        (type == ".sv") || clp->fullSVMode() || clp->isSVFile(fileId);
  }

  m_antlrParserHandler->m_lexer->removeErrorListeners();
  m_antlrParserHandler->m_lexer->addErrorListener(
      m_antlrParserHandler->m_errorListener);
  m_antlrParserHandler->m_tokens =
      new antlr4::CommonTokenStream(m_antlrParserHandler->m_lexer);
  m_antlrParserHandler->m_tokens->fill();

  if (getCompileSourceFile()->getCommandLineParser()->profile()) {
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

  if (getCompileSourceFile()->getCommandLineParser()->profile()) {
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

    if (getCompileSourceFile()->getCommandLineParser()->profile()) {
      StrAppend(&m_profileInfo,
                "SLL Parsing: ", StringUtils::to_string(tmr.elapsed_rounded()),
                "s ", fileSystem->toPath(fileId), "\n");
      tmr.reset();
      profileParser();
    }
  } catch (antlr4::ParseCancellationException& pex) {
    m_antlrParserHandler->m_tokens->reset();
    m_antlrParserHandler->m_parser->reset();
    m_antlrParserHandler->m_parser->removeErrorListeners();
    if (getCompileSourceFile()->getCommandLineParser()->profile()) {
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

    if (getCompileSourceFile()->getCommandLineParser()->profile()) {
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
  FileSystem* const fileSystem = FileSystem::getInstance();
  CommandLineParser* clp = getCompileSourceFile()->getCommandLineParser();
  Precompiled* prec = Precompiled::getSingleton();
  bool precompiled = prec->isFilePrecompiled(m_ppFileId, getSymbolTable());

  if (m_children.empty()) {
    ParseCache cache(this);

    if (cache.restore()) {
      m_usingCachedVersion = true;
      if (debug_AstModel && !precompiled)
        std::cout << m_fileContent->printObjects();
      if (clp->debugCache()) {
        std::cout << "PARSER CACHE USED FOR: "
                  << fileSystem->toPath(getFileId(0)) << std::endl;
      }
      return true;
    }
  } else {
    bool ok = true;
    for (ParseFile* child : m_children) {
      ParseCache cache(child);

      if (cache.restore()) {
        child->m_fileContent->setParent(m_fileContent);
        m_usingCachedVersion = true;
        if (debug_AstModel && !precompiled)
          std::cout << child->m_fileContent->printObjects();
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

      m_listener = new SV3_1aTreeShapeListener(
          this, m_antlrParserHandler->m_tokens, m_offsetLine);
      antlr4::tree::ParseTreeWalker::DEFAULT.walk(m_listener,
                                                  m_antlrParserHandler->m_tree);

      if (debug_AstModel && !precompiled)
        std::cout << m_fileContent->printObjects();

      if (clp->profile()) {
        // m_profileInfo += "AST Walking: " + std::to_string
        // (tmr.elapsed_rounded ()) + "\n";
        tmr.reset();
      }

      ParseCache cache(this);
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
          child->m_listener = new SV3_1aTreeShapeListener(
              child, child->m_antlrParserHandler->m_tokens,
              child->m_offsetLine);

          Timer tmr;
          antlr4::tree::ParseTreeWalker::DEFAULT.walk(
              child->m_listener, child->m_antlrParserHandler->m_tree);

          if (clp->profile()) {
            // m_profileInfo += "For file " + getSymbol
            // (child->m_ppFileId) + ", AST Walking took" +
            // std::to_string (tmr.elapsed_rounded ()) + "\n";
            tmr.reset();
          }

          if (debug_AstModel && !precompiled)
            std::cout << child->m_fileContent->printObjects();

          ParseCache cache(child);
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
