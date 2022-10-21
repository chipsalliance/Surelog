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
 * File:   SVLibShapeListener.cpp
 * Author: alain
 *
 * Created on January 28, 2018, 10:17 PM
 */

#include <Surelog/CommandLine/CommandLineParser.h>
#include <Surelog/Common/FileSystem.h>
#include <Surelog/Design/FileContent.h>
#include <Surelog/ErrorReporting/ErrorContainer.h>
#include <Surelog/Library/Library.h>
#include <Surelog/Library/LibrarySet.h>
#include <Surelog/Library/ParseLibraryDef.h>
#include <Surelog/Library/SVLibShapeListener.h>
#include <Surelog/SourceCompile/ParseFile.h>
#include <Surelog/SourceCompile/SymbolTable.h>
#include <Surelog/Utils/ParseUtils.h>

#include <regex>

namespace SURELOG {
SVLibShapeListener::SVLibShapeListener(ParseLibraryDef *parser,
                                       antlr4::CommonTokenStream *tokens)
    : SV3_1aTreeShapeHelper(
          new ParseFile(parser->getFileId(), parser->getSymbolTable(),
                        parser->getErrorContainer()),
          tokens, 0),
      m_parser(parser),
      m_tokens(tokens) {
  m_fileContent = new FileContent(
      m_parser->getFileId(), nullptr, m_parser->getSymbolTable(),
      m_parser->getErrorContainer(), nullptr, BadPathId);
  m_pf->setFileContent(m_fileContent);
  m_includeFileInfo.emplace(IncludeFileInfo::Context::NONE, 1,
                            m_pf->getFileId(0), 0, 0, 0, 0,
                            IncludeFileInfo::Action::PUSH);
}

SymbolId SVLibShapeListener::registerSymbol(std::string_view symbol) {
  return m_parser->getSymbolTable()->registerSymbol(symbol);
}

void SVLibShapeListener::enterLibrary_declaration(
    SV3_1aParser::Library_declarationContext *ctx) {
  FileSystem *const fileSystem = FileSystem::getInstance();
  std::string name = ctx->identifier()->getText();
  LibrarySet *librarySet = m_parser->getLibrarySet();
  Library *lib = librarySet->addLibrary(name, m_parser->getSymbolTable());
  SymbolTable *symbolTable = m_parser->getSymbolTable();
  PathId baseDirId = fileSystem->getParent(m_parser->getFileId(), symbolTable);
  for (auto pathSpec : ctx->file_path_spec()) {
    PathIdVector fileIds;
    fileSystem->matching(baseDirId, pathSpec->getText(), symbolTable, fileIds);
    for (const auto &id : fileIds) {
      lib->addFileId(id);
      std::string_view type = std::get<1>(fileSystem->getType(id, symbolTable));
      if ((type == ".cfg") || (type == ".map")) {
        ParseLibraryDef parser(m_parser->getCommandLineParser(),
                               m_parser->getErrorContainer(), symbolTable,
                               librarySet, m_parser->getConfigSet());
        parser.parseLibraryDefinition(id, lib);
      }
    }
  }
}

void SVLibShapeListener::enterInclude_statement(
    SV3_1aParser::Include_statementContext *ctx) {
  const std::string filename = ctx->file_path_spec()->getText();

  FileSystem *const fileSystem = FileSystem::getInstance();
  SymbolTable *const symbolTable = m_parser->getSymbolTable();

  const PathIdVector &includePathIds =
      m_parser->getCommandLineParser()->getIncludePaths();
  PathId fileId = fileSystem->locate(filename, includePathIds, symbolTable);

  if (!fileId) {
    fileId =
        fileSystem->getSibling(m_parser->getFileId(), filename, symbolTable);
  }

  if (!fileId || !fileSystem->isRegularFile(fileId)) {
    std::pair<int, int> lineCol = ParseUtils::getLineColumn(m_tokens, ctx);
    Location loc(m_parser->getFileId(), lineCol.first, lineCol.second,
                 symbolTable->registerSymbol(filename));
    Error err(ErrorDefinition::PP_CANNOT_OPEN_INCLUDE_FILE, loc);
    m_parser->getErrorContainer()->addError(err);
    return;
  }

  ParseLibraryDef parser(m_parser->getCommandLineParser(),
                         m_parser->getErrorContainer(), symbolTable,
                         m_parser->getLibrarySet(), m_parser->getConfigSet());
  parser.parseLibraryDefinition(fileId);
}

void SVLibShapeListener::enterUselib_directive(
    SV3_1aParser::Uselib_directiveContext *ctx) {}

void SVLibShapeListener::enterConfig_declaration(
    SV3_1aParser::Config_declarationContext *ctx) {}

void SVLibShapeListener::enterDesign_statement(
    SV3_1aParser::Design_statementContext *ctx) {}

void SVLibShapeListener::enterConfig_rule_statement(
    SV3_1aParser::Config_rule_statementContext *ctx) {}

void SVLibShapeListener::enterDefault_clause(
    SV3_1aParser::Default_clauseContext *ctx) {}

void SVLibShapeListener::enterInst_clause(
    SV3_1aParser::Inst_clauseContext *ctx) {}

void SVLibShapeListener::enterInst_name(SV3_1aParser::Inst_nameContext *ctx) {}

void SVLibShapeListener::enterCell_clause(
    SV3_1aParser::Cell_clauseContext *ctx) {}

void SVLibShapeListener::enterLiblist_clause(
    SV3_1aParser::Liblist_clauseContext *ctx) {}

void SVLibShapeListener::enterUse_clause(SV3_1aParser::Use_clauseContext *ctx) {

}

void SVLibShapeListener::exitString_value(
    SV3_1aParser::String_valueContext *ctx) {
  std::string ident;

  ident = ctx->String()->getText();

  addVObject(ctx, ident, VObjectType::slStringLiteral);

  if (ident.size() > SV_MAX_STRING_SIZE) {
    logError(ErrorDefinition::PA_MAX_LENGTH_IDENTIFIER, ctx, ident);
  }
}

void SVLibShapeListener::exitIdentifier(SV3_1aParser::IdentifierContext *ctx) {
  std::string ident;
  if (ctx->Simple_identifier())
    ident = ctx->Simple_identifier()->getText();
  else if (ctx->Escaped_identifier()) {
    ident = ctx->Escaped_identifier()->getText();
    ident.erase(0, 3);
    ident.erase(ident.size() - 3, 3);
  } else if (ctx->THIS())
    ident = ctx->THIS()->getText();
  else if (ctx->RANDOMIZE())
    ident = ctx->RANDOMIZE()->getText();
  else if (ctx->SAMPLE())
    ident = ctx->SAMPLE()->getText();

  // !!! Don't forget to change CompileModule.cpp type checker !!!
  addVObject(ctx, ident, VObjectType::slStringConst);

  if (ident.size() > SV_MAX_IDENTIFIER_SIZE) {
    logError(ErrorDefinition::PA_MAX_LENGTH_IDENTIFIER, ctx, ident);
  }
}

void SVLibShapeListener::exitHierarchical_identifier(
    SV3_1aParser::Hierarchical_identifierContext *ctx) {
  std::string ident;
  antlr4::ParserRuleContext *childCtx = nullptr;

  childCtx = (antlr4::ParserRuleContext *)ctx->children[0];
  ident = ctx->getText();
  ident = std::regex_replace(ident, std::regex(EscapeSequence), "");
  addVObject(childCtx, ident, VObjectType::slStringConst);
  addVObject(ctx, VObjectType::slHierarchical_identifier);

  if (ident.size() > SV_MAX_IDENTIFIER_SIZE) {
    logError(ErrorDefinition::PA_MAX_LENGTH_IDENTIFIER, ctx, ident);
  }
}
}  // namespace SURELOG
