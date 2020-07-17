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

#include "SourceCompile/SymbolTable.h"
#include "CommandLine/CommandLineParser.h"
#include "ErrorReporting/ErrorContainer.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/Compiler.h"
#include "SourceCompile/ParseFile.h"
#include "SourceCompile/AntlrParserHandler.h"
#include <cstdlib>
#include <iostream>
#include "antlr4-runtime.h"
#include "atn/ParserATNSimulator.h"

using namespace std;
using namespace antlr4;
using namespace SURELOG;

#include "parser/SV3_1aLexer.h"
#include "parser/SV3_1aParser.h"
#include "parser/SV3_1aParserBaseListener.h"
#include "SourceCompile/SV3_1aTreeShapeListener.h"
#include "API/SV3_1aPythonListener.h"
using namespace antlr4;
#include "Utils/ParseUtils.h"
#include "Utils/FileUtils.h"
#include "Cache/ParseCache.h"
#include "SourceCompile/AntlrParserErrorListener.h"
#include "Package/Precompiled.h"
#include "Utils/StringUtils.h"
#include "Utils/Timer.h"

ParseFile::ParseFile(SymbolId fileId, SymbolTable* symbolTable,
                     ErrorContainer* errors)
    : m_fileId(fileId),
      m_ppFileId(0),
      m_compileSourceFile(NULL),
      m_compilationUnit(NULL),
      m_library(NULL),
      m_antlrParserHandler(NULL),
      m_listener(NULL),
      m_usingCachedVersion(false),
      m_keepParserHandler(false),
      m_fileContent(NULL),
      debug_AstModel(false),
      m_parent(NULL),
      m_offsetLine(0),
      m_symbolTable(symbolTable),
      m_errors(errors) {
  debug_AstModel = false;
}

ParseFile::ParseFile(SymbolId fileId, CompileSourceFile* csf,
                     CompilationUnit* compilationUnit, Library* library,
                     SymbolId ppFileId, bool keepParserHandler)
    : m_fileId(fileId),
      m_ppFileId(ppFileId),
      m_compileSourceFile(csf),
      m_compilationUnit(compilationUnit),
      m_library(library),
      m_antlrParserHandler(NULL),
      m_listener(NULL),
      m_usingCachedVersion(false),
      m_keepParserHandler(keepParserHandler),
      m_fileContent(NULL),
      debug_AstModel(false),
      m_parent(NULL),
      m_offsetLine(0),
      m_symbolTable(NULL),
      m_errors(NULL) {
  debug_AstModel =
      m_compileSourceFile->getCommandLineParser()->getDebugAstModel();
}

ParseFile::ParseFile(CompileSourceFile* compileSourceFile, ParseFile* parent,
                     SymbolId chunkFileId, unsigned int offsetLine)
    : m_fileId(parent->m_fileId),
      m_ppFileId(chunkFileId),
      m_compileSourceFile(compileSourceFile),
      m_compilationUnit(parent->m_compilationUnit),
      m_library(parent->m_library),
      m_antlrParserHandler(NULL),
      m_listener(NULL),
      m_usingCachedVersion(false),
      m_keepParserHandler(parent->m_keepParserHandler),
      m_fileContent(parent->m_fileContent),
      debug_AstModel(false),
      m_parent(parent),
      m_offsetLine(offsetLine),
      m_symbolTable(NULL),
      m_errors(NULL) {
  parent->m_children.push_back(this);
}

ParseFile::~ParseFile() {
  if (!m_keepParserHandler) delete m_antlrParserHandler;
}

SymbolTable* ParseFile::getSymbolTable() {
  return m_symbolTable ? m_symbolTable : m_compileSourceFile->getSymbolTable();
}

ErrorContainer* ParseFile::getErrorContainer() {
  return m_errors ? m_errors : m_compileSourceFile->getErrorContainer();
}

SymbolId ParseFile::registerSymbol(const std::string symbol) {
  return getCompileSourceFile()->getSymbolTable()->registerSymbol(symbol);
}

SymbolId ParseFile::getId(const std::string symbol) {
  return getCompileSourceFile()->getSymbolTable()->getId(symbol);
}

const std::string ParseFile::getSymbol(SymbolId id) {
  return getCompileSourceFile()->getSymbolTable()->getSymbol(id);
}

const std::string ParseFile::getFileName(unsigned int line) {
  return getSymbol(getFileId(line));
}

void ParseFile::addError(Error& error) {
  getCompileSourceFile()->getErrorContainer()->addError(error);
}

SymbolId ParseFile::getFileId(unsigned int line) {
  if (!getCompileSourceFile()) {
    return m_fileId;
  }
  PreprocessFile* pp = getCompileSourceFile()->getPreprocessor();
  auto& infos = pp->getIncludeFileInfo();
  if (infos.size()) {
    bool inRange = false;
    unsigned int indexOpeningRange = 0;
    unsigned int index = infos.size() - 1;
    while(1) {
      if ((line >= infos[index].m_originalLine) && (infos[index].m_type == 2)) {
        const std::string& file = pp->getSymbol(infos[index].m_sectionFile);
        SymbolId fileId = getSymbolTable()->registerSymbol(file);
        return (fileId);
      }
      if (infos[index].m_type == 2) {
        if (!inRange) {
          inRange = true;
          indexOpeningRange = infos[index].m_indexOpening;
        }
      } else {
        if (inRange) {
          if (index == indexOpeningRange) inRange = false;
        }
      }
      if ((line >= infos[index].m_originalLine) && (infos[index].m_type == 1) &&
          (infos[index].m_indexClosing > -1) && (line < infos[infos[index].m_indexClosing].m_originalLine)) {
        const std::string& file = pp->getSymbol(infos[index].m_sectionFile);
        SymbolId fileId = getSymbolTable()->registerSymbol(file);
        return (fileId);
      }
      if (index == 0) break;
      index--;
    }
    return m_fileId;
  } else {
    return m_fileId;
  }
}

unsigned int ParseFile::getLineNb(unsigned int line) {
  if (!getCompileSourceFile()) return line;
  PreprocessFile* pp = getCompileSourceFile()->getPreprocessor();
  auto& infos = pp->getIncludeFileInfo();
  if (infos.size()) {
    bool inRange = false;
    unsigned int indexOpeningRange = 0;
    unsigned int index = infos.size() - 1;
    while (1) {

      if ((line >= infos[index].m_originalLine) && (infos[index].m_type == 2)) {
        return (infos[index].m_sectionStartLine + (line - infos[index].m_originalLine));
      }

      if (infos[index].m_type == 2) {
        if (!inRange) {
          inRange = true;
          indexOpeningRange = infos[index].m_indexOpening;
        }
      } else {
        if (inRange) {
          if (index == indexOpeningRange) inRange = false;
        }
      }
      if ((line >= infos[index].m_originalLine) && (infos[index].m_type == 1) &&
          (infos[index].m_indexClosing > -1) && (line < infos[infos[index].m_indexClosing].m_originalLine)) {
        return (infos[index].m_sectionStartLine + (line - infos[index].m_originalLine));
      }
      if (index == 0) break;
      index --;
    }
    return line;
  } else {
    return line;
  }
}

bool ParseFile::parseOneFile_(std::string fileName, unsigned int lineOffset) {
  CommandLineParser* clp = getCompileSourceFile()->getCommandLineParser();
  PreprocessFile* pp = getCompileSourceFile()->getPreprocessor();
  Timer tmr;
  AntlrParserHandler* antlrParserHandler = new AntlrParserHandler();
  m_antlrParserHandler = antlrParserHandler;
  std::ifstream stream;
  stream.open(fileName);
  if (!stream.good()) {
    SymbolId fileId = registerSymbol(fileName);
    Location ppfile(fileId);
    Error err(ErrorDefinition::PA_CANNOT_OPEN_FILE, ppfile);
    addError(err);
    return false;
  }

  antlrParserHandler->m_inputStream = new ANTLRInputStream(stream);
  antlrParserHandler->m_errorListener =
      new AntlrParserErrorListener(this, false, lineOffset, fileName);
  antlrParserHandler->m_lexer =
      new SV3_1aLexer(antlrParserHandler->m_inputStream);
  std::string suffix = StringUtils::leaf(fileName);
  VerilogVersion version = pp->getVerilogVersion();
  if (version != VerilogVersion::NoVersion) {
    switch (version) {
    case VerilogVersion::NoVersion:
      break;
    case VerilogVersion::Verilog1995:
      antlrParserHandler->m_lexer->sverilog = false;
      break;
    case VerilogVersion::Verilog2001:
      antlrParserHandler->m_lexer->sverilog = false;
      break;
    case VerilogVersion::Verilog2005:
      antlrParserHandler->m_lexer->sverilog = true;
      break;
    case VerilogVersion::Verilog2009:
      antlrParserHandler->m_lexer->sverilog = true;
      break;
    case VerilogVersion::SystemVerilog:
      antlrParserHandler->m_lexer->sverilog = true;
      break;
    }
  } else {
    std::string baseFileName = FileUtils::basename(fileName);
    if ((suffix == "sv") || (clp->fullSVMode()) || (clp->isSVFile(baseFileName))) {
      antlrParserHandler->m_lexer->sverilog = true;
    } else {
      antlrParserHandler->m_lexer->sverilog = false;
    }
  }

  antlrParserHandler->m_lexer->removeErrorListeners();
  antlrParserHandler->m_lexer->addErrorListener(
      antlrParserHandler->m_errorListener);
  antlrParserHandler->m_tokens =
      new CommonTokenStream(antlrParserHandler->m_lexer);
  antlrParserHandler->m_tokens->fill();

  if (getCompileSourceFile()->getCommandLineParser()->profile()) {
    // m_profileInfo += "Tokenizer: " + std::to_string (tmr.elapsed_rounded ())
    // + " " + fileName + "\n";
    tmr.reset();
  }

  antlrParserHandler->m_parser = new SV3_1aParser(antlrParserHandler->m_tokens);

  m_antlrParserHandler->m_parser->getInterpreter<atn::ParserATNSimulator>()
      ->setPredictionMode(atn::PredictionMode::SLL);
  m_antlrParserHandler->m_parser->setErrorHandler(
      std::make_shared<BailErrorStrategy>());
  m_antlrParserHandler->m_parser->removeErrorListeners();

  try {
    m_antlrParserHandler->m_tree =
        m_antlrParserHandler->m_parser->top_level_rule();

    if (getCompileSourceFile()->getCommandLineParser()->profile()) {
      m_profileInfo +=
          "SLL Parsing: " + StringUtils::to_string(tmr.elapsed_rounded()) +
          "s " + fileName + "\n";
      tmr.reset();
    }
  } catch (ParseCancellationException& pex) {
    m_antlrParserHandler->m_tokens->reset();
    m_antlrParserHandler->m_parser->reset();

    m_antlrParserHandler->m_parser->setErrorHandler(
        std::make_shared<DefaultErrorStrategy>());
    antlrParserHandler->m_parser->removeErrorListeners();
    antlrParserHandler->m_parser->addErrorListener(
        antlrParserHandler->m_errorListener);
    antlrParserHandler->m_parser->getInterpreter<atn::ParserATNSimulator>()
        ->setPredictionMode(atn::PredictionMode::LL);
    antlrParserHandler->m_tree = antlrParserHandler->m_parser->top_level_rule();

    if (getCompileSourceFile()->getCommandLineParser()->profile()) {
      m_profileInfo +=
          "LL  Parsing: " + StringUtils::to_string(tmr.elapsed_rounded()) +
          " " + fileName + "\n";
      tmr.reset();
    }
  }
  stream.close();
  return true;
}

std::string ParseFile::getProfileInfo() {
  std::string profile;
  profile = m_profileInfo;
  for (unsigned int i = 0; i < m_children.size(); i++)
    profile += m_children[i]->m_profileInfo;

  return profile;
}

bool ParseFile::parse() {
  Precompiled* prec = Precompiled::getSingleton();
  std::string root = FileUtils::basename(this->getPpFileName());
  bool precompiled = false;
  if (prec->isFilePrecompiled(root)) precompiled = true;

  if (m_children.size() == 0) {
    ParseCache cache(this);

    if (cache.restore()) {
      m_usingCachedVersion = true;
      if (debug_AstModel && !precompiled)
        std::cout << m_fileContent->printObjects();
      return true;
    }
 } else {
    bool ok = true;
    for (unsigned int i = 0; i < m_children.size(); i++) {
      ParseCache cache(m_children[i]);

      if (cache.restore()) {
        m_children[i]->m_fileContent->setParent(m_fileContent);
        m_usingCachedVersion = true;
        if (debug_AstModel && !precompiled)
          std::cout << m_children[i]->m_fileContent->printObjects();
      } else {
        ok = false;
      }
    }
    if (ok) {
      return true;
    }
  }

  // This is not a parent Parser object
  if (m_children.size() == 0) {
    // std::cout << std::endl << "Parsing " << getSymbol(m_ppFileId) << " Line:
    // " << m_offsetLine << std::endl << std::flush;

    parseOneFile_(getSymbol(m_ppFileId), m_offsetLine);

    // m_listener = new SV3_1aTreeShapeListener (this,
    // m_antlrParserHandler->m_tokens, m_offsetLine);
    // tree::ParseTreeWalker::DEFAULT.walk (m_listener,
    // m_antlrParserHandler->m_tree); std::cout << std::endl << "End Parsing " <<
    // getSymbol(m_ppFileId) << " Line: " << m_offsetLine << std::endl <<
    // std::flush;
  }

  // This is either a parent Parser object of this Parser object has no parent
  if ((m_children.size() != 0) || (m_parent == NULL)) {
    if ((m_parent == NULL) && (m_children.size() == 0)) {
      Timer tmr;

      m_listener = new SV3_1aTreeShapeListener(
          this, m_antlrParserHandler->m_tokens, m_offsetLine);
      tree::ParseTreeWalker::DEFAULT.walk(m_listener,
                                          m_antlrParserHandler->m_tree);

      if (debug_AstModel && !precompiled)
        std::cout << m_fileContent->printObjects();

      if (getCompileSourceFile()->getCommandLineParser()->profile()) {
        // m_profileInfo += "AST Walking: " + std::to_string
        // (tmr.elapsed_rounded ()) + "\n";
        tmr.reset();
      }

      ParseCache cache(this);
      if (!cache.save()) {
        return false;
      }

      if (getCompileSourceFile()->getCommandLineParser()->profile()) {
        m_profileInfo += "Cache saving: " + std::to_string(tmr.elapsed_rounded ()) + "s\n";
        std::cout << "Cache saving: " + std::to_string(tmr.elapsed_rounded ()) + "s\n" << std::flush;
        tmr.reset();
      }
    }

    if (m_children.size() != 0) {
      for (unsigned int i = 0; i < m_children.size(); i++) {
        if (m_children[i]->m_antlrParserHandler) {
          // Only visit the chunks that got re-parsed
          // TODO: Incrementally regenerate the FileContent
          m_children[i]->m_fileContent->setParent(m_fileContent);
          m_children[i]->m_listener = new SV3_1aTreeShapeListener(
              m_children[i], m_children[i]->m_antlrParserHandler->m_tokens,
              m_children[i]->m_offsetLine);

          Timer tmr;
          tree::ParseTreeWalker::DEFAULT.walk(
              m_children[i]->m_listener,
              m_children[i]->m_antlrParserHandler->m_tree);

          if (getCompileSourceFile()->getCommandLineParser()->profile()) {
            // m_profileInfo += "For file " + getSymbol
            // (m_children[i]->m_ppFileId) + ", AST Walking took" +
            // std::to_string (tmr.elapsed_rounded ()) + "\n";
            tmr.reset();
          }

          if (debug_AstModel && !precompiled)
            std::cout << m_children[i]->m_fileContent->printObjects();

          ParseCache cache(m_children[i]);
          if (!cache.save()) {
            return false;
          }
        }
      }
    }
  }
  return true;
}
