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

#include <Surelog/CommandLine/CommandLineParser.h>
#include <Surelog/Common/FileSystem.h>
#include <Surelog/Config/ConfigSet.h>
#include <Surelog/Design/FileContent.h>
#include <Surelog/ErrorReporting/ErrorContainer.h>
#include <Surelog/Library/AntlrLibParserErrorListener.h>
#include <Surelog/Library/Library.h>
#include <Surelog/Library/LibrarySet.h>
#include <Surelog/Library/ParseLibraryDef.h>
#include <Surelog/Library/SVLibShapeListener.h>
#include <Surelog/SourceCompile/SymbolTable.h>
#include <Surelog/Utils/StringUtils.h>
#include <parser/SV3_1aLexer.h>
#include <parser/SV3_1aParser.h>

namespace SURELOG {

ParseLibraryDef::ParseLibraryDef(CommandLineParser* commandLineParser,
                                 ErrorContainer* errors,
                                 SymbolTable* symbolTable,
                                 LibrarySet* librarySet, ConfigSet* configSet)
    : m_commandLineParser(commandLineParser),
      m_errors(errors),
      m_symbolTable(symbolTable),
      m_librarySet(librarySet),
      m_configSet(configSet),
      m_fileContent(nullptr) {}

bool ParseLibraryDef::parseLibrariesDefinition() {
  FileSystem* const fileSystem = FileSystem::getInstance();
  // Get .map files from command line
  std::vector<PathId> libraryMapFiles =
      m_commandLineParser->getLibraryMapFiles();
  if (libraryMapFiles.empty()) {
    // or scan local dir
    for (const PathId& wdId : m_commandLineParser->getWorkingDirs()) {
      fileSystem->collect(wdId, ".map", m_symbolTable, libraryMapFiles);
    }
  }

  // If "work" library is not yet declared from command line, create it
  constexpr std::string_view workN = "work";
  m_librarySet->addLibrary(workN, m_symbolTable);

  // Config files are parsed using the library top rule
  const PathIdVector& cfgFiles = m_commandLineParser->getConfigFiles();
  libraryMapFiles.insert(libraryMapFiles.end(), cfgFiles.begin(),
                         cfgFiles.end());

  for (const PathId& fileId : libraryMapFiles) {
    parseLibraryDefinition(fileId);
  }

  for (const PathId& fileId : cfgFiles) {
    // Register configuration files in "work" library
    m_librarySet->getLibrary(fileId);
  }

  for (const PathId& fileId : m_commandLineParser->getSourceFiles()) {
    // Register files in "work" library
    m_librarySet->getLibrary(fileId);
  }

  m_librarySet->checkErrors(m_symbolTable, m_errors);

  if (m_commandLineParser->getDebugLibraryDef()) {
    m_librarySet->report(std::cout) << std::endl;
  }
  return true;
}

bool ParseLibraryDef::parseLibraryDefinition(PathId fileId, Library* lib) {
  FileSystem* const fileSystem = FileSystem::getInstance();
  m_fileId = fileId;
  std::istream& stream = fileSystem->openForRead(m_fileId);

  if (!stream.good()) {
    fileSystem->close(stream);

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

  SVLibShapeListener* listener = new SVLibShapeListener(this, tokens);
  m_fileContent = listener->getFileContent();

  antlr4::tree::ParseTreeWalker::DEFAULT.walk(listener, m_tree);

  if (m_fileContent->getLibrary() == nullptr) {
    if (lib) {
      m_fileContent->setLibrary(lib);
    } else {
      m_fileContent->setLibrary(m_librarySet->getLibrary(m_fileId));
    }
  }

  if (m_commandLineParser->getDebugAstModel()) {
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
  FileContent* fC = m_fileContent;
  if (!fC) return false;

  VObjectTypeUnorderedSet types = {VObjectType::slConfig_declaration};
  std::vector<NodeId> configs = fC->sl_collect_all(fC->getRootNode(), types);
  for (auto config : configs) {
    NodeId ident = fC->Child(config);
    std::string name =
        StrCat(fC->getLibrary()->getName(), "@", fC->SymName(ident));
    m_symbolTable->registerSymbol(name);
    Config conf(name, fC, config);

    // Design clause
    VObjectTypeUnorderedSet designStmt = {VObjectType::slDesign_statement};
    std::vector<NodeId> designs = fC->sl_collect_all(config, designStmt);
    if (designs.empty()) {
      // TODO: Error
    } else if (designs.size() > 1) {
      // TODO: Error
    } else {
      NodeId design = designs[0];
      NodeId libName = fC->Child(design);
      NodeId topName = fC->Sibling(libName);
      if (!topName) {
        conf.setDesignLib(fC->getLibrary()->getName());
        conf.setDesignTop(fC->SymName(libName));
      } else {
        conf.setDesignLib(fC->SymName(libName));
        conf.setDesignTop(fC->SymName(topName));
      }
    }

    // Default clause
    VObjectTypeUnorderedSet defaultStmt = {VObjectType::slDefault_clause};
    std::vector<NodeId> defaults = fC->sl_collect_all(config, defaultStmt);
    if (!defaults.empty()) {
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
    VObjectTypeUnorderedSet instanceStmt = {VObjectType::slInst_clause,
                                            VObjectType::slCell_clause};
    std::vector<NodeId> instances = fC->sl_collect_all(config, instanceStmt);
    for (auto inst : instances) {
      VObjectType type = fC->Type(inst);
      NodeId instName = fC->Child(inst);
      if (type == VObjectType::slInst_clause) instName = fC->Child(instName);
      std::string instNameS;
      while (instName) {
        if (instNameS.empty())
          instNameS = fC->SymName(instName);
        else
          instNameS.append(".").append(fC->SymName(instName));
        instName = fC->Sibling(instName);
      }
      NodeId instClause = fC->Sibling(inst);
      if (fC->Type(instClause) == VObjectType::slLiblist_clause) {
        NodeId libList = fC->Child(instClause);
        std::vector<std::string> libs;
        while (libList) {
          libs.emplace_back(fC->SymName(libList));
          libList = fC->Sibling(libList);
        }

        UseClause usec(UseClause::UseLib, libs, fC, instClause);
        if (type == VObjectType::slInst_clause)
          conf.addInstanceUseClause(instNameS, usec);
        else
          conf.addCellUseClause(instNameS, usec);
      } else if (fC->Type(instClause) == VObjectType::slUse_clause) {
        NodeId use = fC->Child(instClause);
        std::string useName;
        VObjectType useType = fC->Type(use);
        if (useType == VObjectType::slParameter_value_assignment) {
          UseClause usec(UseClause::UseParam, fC, use);
          conf.addInstanceUseClause(instNameS, usec);
        } else {
          NodeId mem = use;
          while (use) {
            if (useName.empty())
              useName = fC->SymName(use);
            else
              useName.append(".").append(fC->SymName(use));
            use = fC->Sibling(use);
          }
          useName = StringUtils::replaceAll(useName, ".", "@");
          UseClause usec(UseClause::UseModule, useName, fC, mem);
          if (type == VObjectType::slInst_clause)
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
            useName.append("@").append(fC->SymName(use));
          use = fC->Sibling(use);
        }
        UseClause usec(UseClause::UseConfig, useName, fC, mem);
        if (type == VObjectType::slInst_clause)
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
