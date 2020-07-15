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
 * File:   ParseLibraryDef.cpp
 * Author: alain
 *
 * Created on January 27, 2018, 5:05 PM
 */
#include "Utils/StringUtils.h"
#include "CommandLine/CommandLineParser.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/Compiler.h"
#include "SourceCompile/ParseFile.h"
#include "Library/ParseLibraryDef.h"
#include "Utils/FileUtils.h"
#include "antlr4-runtime.h"
#include "atn/ParserATNSimulator.h"
using namespace antlr4;
using namespace SURELOG;
#include "parser/SV3_1aLexer.h"
#include "parser/SV3_1aParser.h"
#include "Library/SVLibShapeListener.h"
#include "Library/AntlrLibParserErrorListener.h"

ParseLibraryDef::ParseLibraryDef(CommandLineParser* commandLineParser,
                                 ErrorContainer* errors,
                                 SymbolTable* symbolTable,
                                 LibrarySet* librarySet, ConfigSet* configSet)
    : m_fileId(0),
      m_commandLineParser(commandLineParser),
      m_errors(errors),
      m_symbolTable(symbolTable),
      m_librarySet(librarySet),
      m_configSet(configSet),
      m_fileContent(NULL) {}

bool ParseLibraryDef::parseLibrariesDefinition() {
  // Get .map files from command line
  std::vector<SymbolId> libraryMapFiles =
      m_commandLineParser->getLibraryMapFiles();
  if (libraryMapFiles.empty()) {
    // or scan local dir
    libraryMapFiles = FileUtils::collectFiles("./", ".map", m_symbolTable);
  }

  // If "work" library is not yet declared from command line, create it
  std::string workN = "work";
  if (m_librarySet->getLibrary(workN) == NULL) {
    Library work(workN, m_symbolTable);
    m_librarySet->addLibrary(work);
  }

  // Config files are parsed using the library top rule
  std::vector<SymbolId> cfgFiles = m_commandLineParser->getConfigFiles();
  for (auto file : cfgFiles) {
    libraryMapFiles.push_back(file);
  }

  for (auto fileId : libraryMapFiles) {
    parseLibraryDefinition(fileId);
  }

  for (auto file : cfgFiles) {
    std::string fullPath =
        FileUtils::getFullPath(m_symbolTable->getSymbol(file));
    m_librarySet->getLibrary(m_symbolTable->registerSymbol(
        fullPath));  // Register configuration files in "work" library
  }

  unsigned int size = m_commandLineParser->getSourceFiles().size();
  for (unsigned int i = 0; i < size; i++) {
    SymbolId id = m_commandLineParser->getSourceFiles()[i];
    std::string fullPath = FileUtils::getFullPath(m_symbolTable->getSymbol(id));
    m_librarySet->getLibrary(m_symbolTable->registerSymbol(
        fullPath));  // Register files in "work" library
  }

  m_librarySet->checkErrors(m_symbolTable, m_errors);

  if (m_commandLineParser->getDebugLibraryDef()) {
    std::cout << m_librarySet->report(m_symbolTable) << std::endl;
  }
  return true;
}

bool ParseLibraryDef::parseLibraryDefinition(SymbolId fileId, Library* lib) {
  m_fileId = fileId;
  std::string fileName = m_symbolTable->getSymbol(fileId);
  std::string relativePath = FileUtils::getPathName(fileName);
  std::ifstream stream;
  stream.open(fileName);

  if (!stream.good()) {
    Location ppfile(fileId);
    Error err(ErrorDefinition::PA_CANNOT_OPEN_FILE, ppfile);
    m_errors->addError(err);
    return false;
  }

  Location ppfile(fileId);
  Error err(ErrorDefinition::PP_PROCESSING_SOURCE_FILE, ppfile);
  m_errors->addError(err);
  m_errors->printMessage(err, m_commandLineParser->muteStdout());

  AntlrLibParserErrorListener* errorListener =
      new AntlrLibParserErrorListener(this);
  antlr4::ANTLRInputStream* m_inputStream = new ANTLRInputStream(stream);
  SV3_1aLexer* m_lexer = new SV3_1aLexer(m_inputStream);
  m_lexer->removeErrorListeners();
  m_lexer->addErrorListener(errorListener);
  antlr4::CommonTokenStream* m_tokens = new CommonTokenStream(m_lexer);
  m_tokens->fill();
  SV3_1aParser* m_parser = new SV3_1aParser(m_tokens);
  m_parser->removeErrorListeners();
  m_parser->addErrorListener(errorListener);
  antlr4::tree::ParseTree* m_tree = m_parser->top_level_library_rule();

  SVLibShapeListener* m_listener =
      new SVLibShapeListener(this, m_tokens, relativePath);
  m_fileContent = m_listener->getFileContent();

  tree::ParseTreeWalker::DEFAULT.walk(m_listener, m_tree);

  if (m_fileContent->getLibrary() == NULL) {
    if (lib) {
      m_fileContent->setLibrary(lib);
    } else {
      std::string fullPath =
          FileUtils::getFullPath(m_symbolTable->getSymbol(m_fileId));
      m_fileContent->setLibrary(
          m_librarySet->getLibrary(m_symbolTable->registerSymbol(fullPath)));
    }
  }

  if (m_commandLineParser->getDebugAstModel()) {
    std::cout << m_fileContent->printObjects();
  }

  // delete m_tree;
  delete m_parser;
  delete m_tokens;
  delete m_lexer;
  delete m_inputStream;
  delete m_listener;
  return parseConfigDefinition();
}

bool ParseLibraryDef::parseConfigDefinition() {
  FileContent* fC = m_fileContent;
  if (!fC) return false;

  std::vector<VObjectType> types = {VObjectType::slConfig_declaration};
  std::vector<NodeId> configs = fC->sl_collect_all(0, types);
  for (auto config : configs) {
    NodeId ident = fC->Child(config);
    std::string name = fC->getLibrary()->getName() + "@" + fC->SymName(ident);
    m_symbolTable->registerSymbol(name);
    Config conf(name, fC, config);

    // Design clause
    std::vector<VObjectType> designStmt = {VObjectType::slDesign_statement};
    std::vector<NodeId> designs = fC->sl_collect_all(config, designStmt);
    if (designs.size() == 0) {
      // TODO: Error
    } else if (designs.size() > 1) {
      // TODO: Error
    } else {
      NodeId design = designs[0];
      NodeId libName = fC->Child(design);
      NodeId topName = fC->Sibling(libName);
      if (topName == 0) {
        conf.setDesignLib(fC->getLibrary()->getName());
        conf.setDesignTop(fC->SymName(libName));
      } else {
        conf.setDesignLib(fC->SymName(libName));
        conf.setDesignTop(fC->SymName(topName));
      }
    }

    // Default clause
    std::vector<VObjectType> defaultStmt = {VObjectType::slDefault_clause};
    std::vector<NodeId> defaults = fC->sl_collect_all(config, defaultStmt);
    if (defaults.size() > 0) {
      NodeId defaultClause = defaults[0];
      NodeId libList = fC->Sibling(defaultClause);
      if (fC->Type(libList) == VObjectType::slLiblist_clause) {
        NodeId lib = fC->Child(libList);
        while (lib) {
          conf.addDefaultLib(fC->SymName(lib));
          lib = fC->Sibling(lib);
        }
      }
    }

    // Instance and Cell clauses
    std::vector<VObjectType> instanceStmt = {VObjectType::slInst_clause,
                                             VObjectType::slCell_clause};
    std::vector<NodeId> instances = fC->sl_collect_all(config, instanceStmt);
    for (auto inst : instances) {
      VObjectType type = fC->Type(inst);
      NodeId instName = fC->Child(inst);
      if (type == slInst_clause) instName = fC->Child(instName);
      std::string instNameS;
      while (instName) {
        if (instNameS.empty())
          instNameS = fC->SymName(instName);
        else
          instNameS += "." + fC->SymName(instName);
        instName = fC->Sibling(instName);
      }
      NodeId instClause = fC->Sibling(inst);
      if (fC->Type(instClause) == VObjectType::slLiblist_clause) {
        NodeId libList = fC->Child(instClause);
        std::vector<std::string> libs;
        while (libList) {
          libs.push_back(fC->SymName(libList));
          libList = fC->Sibling(libList);
        }

        UseClause usec(UseClause::UseLib, libs, fC, instClause);
        if (type == slInst_clause)
          conf.addInstanceUseClause(instNameS, usec);
        else
          conf.addCellUseClause(instNameS, usec);
      } else if (fC->Type(instClause) == VObjectType::slUse_clause) {
        NodeId use = fC->Child(instClause);
        std::string useName;
        VObjectType useType = fC->Type(use);
        if (useType == slParameter_value_assignment) {
          UseClause usec(UseClause::UseParam, fC, use);
          conf.addInstanceUseClause(instNameS, usec);
        } else {
          NodeId mem = use;
          while (use) {
            if (useName.empty())
              useName = fC->SymName(use);
            else
              useName += "." + fC->SymName(use);
            use = fC->Sibling(use);
          }
          useName = StringUtils::replaceAll(useName, ".", "@");
          UseClause usec(UseClause::UseModule, useName, fC, mem);
          if (type == slInst_clause)
            conf.addInstanceUseClause(instNameS, usec);
          else
            conf.addCellUseClause(instNameS, usec);
        }
      } else if (fC->Type(instClause) == VObjectType::slUse_clause_config) {
        NodeId use = fC->Child(instClause);
        std::string useName;
        NodeId mem = use;
        while (use) {
          if (useName.empty())
            useName = fC->SymName(use);
          else
            useName += "@" + fC->SymName(use);
          use = fC->Sibling(use);
        }
        UseClause usec(UseClause::UseConfig, useName, fC, mem);
        if (type == slInst_clause)
          conf.addInstanceUseClause(instNameS, usec);
        else
          conf.addCellUseClause(instNameS, usec);
      }
    }

    m_configSet->addConfig(conf);
  }

  return true;
}
