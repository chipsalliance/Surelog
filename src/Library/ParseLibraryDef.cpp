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

#include "Surelog/Library/ParseLibraryDef.h"

#include <antlr4-runtime.h>
#include <parser/SV3_1aLexer.h>
#include <parser/SV3_1aParser.h>

#include <iostream>
#include <string>
#include <vector>

#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Common/NodeId.h"
#include "Surelog/Common/PathId.h"
#include "Surelog/Common/Session.h"
#include "Surelog/Config/ConfigSet.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/ErrorReporting/Error.h"
#include "Surelog/ErrorReporting/ErrorContainer.h"
#include "Surelog/ErrorReporting/ErrorDefinition.h"
#include "Surelog/ErrorReporting/Location.h"
#include "Surelog/Library/AntlrLibParserErrorListener.h"
#include "Surelog/Library/Library.h"
#include "Surelog/Library/LibrarySet.h"
#include "Surelog/Library/SVLibShapeListener.h"
#include "Surelog/SourceCompile/SymbolTable.h"
#include "Surelog/SourceCompile/VObjectTypes.h"
#include "Surelog/Utils/StringUtils.h"

namespace SURELOG {

ParseLibraryDef::ParseLibraryDef(Session* session, LibrarySet* librarySet,
                                 ConfigSet* configSet)
    : m_session(session),
      m_librarySet(librarySet),
      m_configSet(configSet),
      m_fileContent(nullptr) {}

bool ParseLibraryDef::parseLibrariesDefinition() {
  // Get .map files from command line
  SymbolTable* const symbols = m_session->getSymbolTable();
  FileSystem* const fileSystem = m_session->getFileSystem();
  ErrorContainer* const errors = m_session->getErrorContainer();
  CommandLineParser* const clp = m_session->getCommandLineParser();
  std::vector<PathId> libraryMapFiles = clp->getLibraryMapFiles();
  if (libraryMapFiles.empty()) {
    // or scan local dir
    for (const PathId& wdId : clp->getWorkingDirs()) {
      fileSystem->collect(wdId, ".map", symbols, libraryMapFiles);
    }
  }

  // If "work" library is not yet declared from command line, create it
  constexpr std::string_view workN = "work";
  m_librarySet->addLibrary(m_session, workN);

  // Config files are parsed using the library top rule
  const PathIdVector& cfgFiles = clp->getConfigFiles();
  libraryMapFiles.insert(libraryMapFiles.end(), cfgFiles.begin(),
                         cfgFiles.end());

  for (const PathId& fileId : libraryMapFiles) {
    parseLibraryDefinition(fileId);
  }

  for (const PathId& fileId : cfgFiles) {
    // Register configuration files in "work" library
    m_librarySet->getLibrary(fileId);
  }

  for (const PathId& fileId : clp->getSourceFiles()) {
    // Register files in "work" library
    m_librarySet->getLibrary(fileId);
  }

  m_librarySet->checkErrors(symbols, errors);

  if (clp->getDebugLibraryDef()) {
    m_librarySet->report(std::cout) << std::endl;
  }
  return true;
}

bool ParseLibraryDef::parseLibraryDefinition(PathId fileId, Library* lib) {
  m_fileId = fileId;

  FileSystem* const fileSystem = m_session->getFileSystem();
  ErrorContainer* const errors = m_session->getErrorContainer();
  CommandLineParser* const clp = m_session->getCommandLineParser();

  std::istream& stream = fileSystem->openForRead(m_fileId);
  if (!stream.good()) {
    fileSystem->close(stream);

    Location ppfile(fileId);
    Error err(ErrorDefinition::PA_CANNOT_OPEN_FILE, ppfile);
    errors->addError(err);
    return false;
  }

  Location ppfile(fileId);
  Error err(ErrorDefinition::PP_PROCESSING_SOURCE_FILE, ppfile);
  errors->addError(err);
  errors->printMessage(err, clp->muteStdout());

  AntlrLibParserErrorListener* errorListener =
      new AntlrLibParserErrorListener(m_session, this);
  antlr4::ANTLRInputStream* inputStream = new antlr4::ANTLRInputStream(stream);
  SV3_1aLexer* lexer = new SV3_1aLexer(inputStream);
  lexer->removeErrorListeners();
  lexer->addErrorListener(errorListener);
  antlr4::CommonTokenStream* tokens = new antlr4::CommonTokenStream(lexer);
  tokens->fill();
  SV3_1aParser* parser = new SV3_1aParser(tokens);
  parser->removeErrorListeners();
  parser->addErrorListener(errorListener);
  antlr4::tree::ParseTree* m_tree = parser->top_level_library_rule();

  SVLibShapeListener* listener =
      new SVLibShapeListener(m_session, this, tokens);
  m_fileContent = listener->getFileContent();

  antlr4::tree::ParseTreeWalker::DEFAULT.walk(listener, m_tree);

  if (m_fileContent->getLibrary() == nullptr) {
    if (lib) {
      m_fileContent->setLibrary(lib);
    } else {
      m_fileContent->setLibrary(m_librarySet->getLibrary(m_fileId));
    }
  }

  if (clp->getDebugAstModel()) {
    std::cout << m_fileContent->printObjects();
  }

  // delete m_tree;
  delete parser;
  delete tokens;
  delete lexer;
  delete inputStream;
  delete listener;
  fileSystem->close(stream);
  return parseConfigDefinition();
}

bool ParseLibraryDef::parseConfigDefinition() {
  if (!m_fileContent) return false;

  SymbolTable* const symbols = m_session->getSymbolTable();

  VObjectTypeUnorderedSet types = {VObjectType::paConfig_declaration};
  std::vector<NodeId> configs =
      m_fileContent->sl_collect_all(m_fileContent->getRootNode(), types);
  for (auto& config : configs) {
    NodeId ident = m_fileContent->Child(config);
    std::string name = StrCat(m_fileContent->getLibrary()->getName(), "@",
                              m_fileContent->SymName(ident));
    symbols->registerSymbol(name);
    Config conf(name, m_fileContent, config);

    // Design clause
    VObjectTypeUnorderedSet designStmt = {VObjectType::paDesign_statement};
    std::vector<NodeId> designs =
        m_fileContent->sl_collect_all(config, designStmt);
    if (designs.empty()) {
      // TODO: Error
    } else if (designs.size() > 1) {
      // TODO: Error
    } else {
      NodeId design = designs[0];
      NodeId libName = m_fileContent->Child(design);
      NodeId topName = m_fileContent->Sibling(libName);
      if (!topName) {
        conf.setDesignLib(m_fileContent->getLibrary()->getName());
        conf.setDesignTop(m_fileContent->SymName(libName));
      } else {
        conf.setDesignLib(m_fileContent->SymName(libName));
        conf.setDesignTop(m_fileContent->SymName(topName));
      }
    }

    // Default clause
    VObjectTypeUnorderedSet defaultStmt = {VObjectType::paDefault_clause};
    std::vector<NodeId> defaults =
        m_fileContent->sl_collect_all(config, defaultStmt);
    if (!defaults.empty()) {
      NodeId defaultClause = defaults[0];
      NodeId libList = m_fileContent->Sibling(defaultClause);
      if (m_fileContent->Type(libList) == VObjectType::paLiblist_clause) {
        NodeId lib = m_fileContent->Child(libList);
        while (lib) {
          conf.addDefaultLib(m_fileContent->SymName(lib));
          lib = m_fileContent->Sibling(lib);
        }
      }
    }

    // Instance and Cell clauses
    VObjectTypeUnorderedSet instanceStmt = {VObjectType::paInst_clause,
                                            VObjectType::paCell_clause};
    std::vector<NodeId> instances =
        m_fileContent->sl_collect_all(config, instanceStmt);
    for (auto& inst : instances) {
      VObjectType type = m_fileContent->Type(inst);
      NodeId instName = m_fileContent->Child(inst);
      if (type == VObjectType::paInst_clause)
        instName = m_fileContent->Child(instName);
      std::string instNameS;
      while (instName) {
        if (instNameS.empty())
          instNameS = m_fileContent->SymName(instName);
        else
          instNameS.append(".").append(m_fileContent->SymName(instName));
        instName = m_fileContent->Sibling(instName);
      }
      NodeId instClause = m_fileContent->Sibling(inst);
      if (m_fileContent->Type(instClause) == VObjectType::paLiblist_clause) {
        NodeId libList = m_fileContent->Child(instClause);
        std::vector<std::string> libs;
        while (libList) {
          libs.emplace_back(m_fileContent->SymName(libList));
          libList = m_fileContent->Sibling(libList);
        }

        UseClause usec(UseClause::UseLib, libs, m_fileContent, instClause);
        if (type == VObjectType::paInst_clause)
          conf.addInstanceUseClause(instNameS, usec);
        else
          conf.addCellUseClause(instNameS, usec);
      } else if (m_fileContent->Type(instClause) == VObjectType::paUse_clause) {
        NodeId use = m_fileContent->Child(instClause);
        std::string useName;
        VObjectType useType = m_fileContent->Type(use);
        if (useType == VObjectType::paParameter_value_assignment) {
          UseClause usec(UseClause::UseParam, m_fileContent, use);
          conf.addInstanceUseClause(instNameS, usec);
        } else {
          NodeId mem = use;
          while (use) {
            if (useName.empty())
              useName = m_fileContent->SymName(use);
            else
              useName.append(".").append(m_fileContent->SymName(use));
            use = m_fileContent->Sibling(use);
          }
          useName = StringUtils::replaceAll(useName, ".", "@");
          UseClause usec(UseClause::UseModule, useName, m_fileContent, mem);
          if (type == VObjectType::paInst_clause)
            conf.addInstanceUseClause(instNameS, usec);
          else
            conf.addCellUseClause(instNameS, usec);
        }
      } else if (m_fileContent->Type(instClause) ==
                 VObjectType::paUse_clause_config) {
        NodeId use = m_fileContent->Child(instClause);
        std::string useName;
        NodeId mem = use;
        while (use) {
          if (useName.empty())
            useName = m_fileContent->SymName(use);
          else
            useName.append("@").append(m_fileContent->SymName(use));
          use = m_fileContent->Sibling(use);
        }
        UseClause usec(UseClause::UseConfig, useName, m_fileContent, mem);
        if (type == VObjectType::paInst_clause)
          conf.addInstanceUseClause(instNameS, usec);
        else
          conf.addCellUseClause(instNameS, usec);
      }
    }

    m_configSet->addConfig(conf);
  }

  return true;
}
}  // namespace SURELOG
