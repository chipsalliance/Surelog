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
#include "../CommandLine/CommandLineParser.hpp"
#include "../SourceCompile/CompilationUnit.h"
#include "../SourceCompile/PreprocessFile.h"
#include "../SourceCompile/CompileSourceFile.h"
#include "../SourceCompile/Compiler.h"
#include "../SourceCompile/ParseFile.h"
#include "ParseLibraryDef.h"
#include "../Utils/FileUtils.h"
#include "antlr4-runtime.h"
#include "atn/ParserATNSimulator.h"
using namespace antlr4;
#include "ParseLibraryDef.h"
#include "SVLibShapeListener.h"
#include "../Utils/FileUtils.h"
#include "../Utils/ParseUtils.h"
using namespace SURELOG;


SVLibShapeListener::SVLibShapeListener (ParseLibraryDef* parser, antlr4::CommonTokenStream* tokens, std::string relativePath) :
    SV3_1aTreeShapeListener(new ParseFile(parser->getFileId (), parser->getSymbolTable (), parser->getErrorContainer ()), tokens, 0),
        m_parser(parser), m_tokens(tokens), m_currentConfig(NULL), m_relativePath(relativePath) 
{ 
}

SVLibShapeListener::~SVLibShapeListener () { }

void SVLibShapeListener::enterLibrary_declaration(SV3_1aParser::Library_declarationContext * ctx) {
  std::string name = ctx->identifier ()->getText();
  Library* lib = m_parser->getLibrarySet ()->getLibrary (name);
  if (lib == NULL)
    {
      Library lib(name, m_parser->getSymbolTable ());
      m_parser->getLibrarySet ()->addLibrary (lib);
    }
  lib = m_parser->getLibrarySet ()->getLibrary (name);

  for (auto pathSpec : ctx->file_path_spec ())
    {
      for (auto id : FileUtils::collectFiles (m_relativePath + pathSpec->getText (), m_parser->getSymbolTable ()))
        {
          lib->addFileId (id);
          std::string fileName = m_parser->getSymbolTable ()->getSymbol (id);
          if ((fileName.find (".cfg") != std::string::npos) ||
              (fileName.find (".map") != std::string::npos))
            {
              ParseLibraryDef parser (m_parser->getCommandLineParser (), m_parser->getErrorContainer (),
                                      m_parser->getSymbolTable (),
                                      m_parser->getLibrarySet (), m_parser->getConfigSet ());
              parser.parseLibraryDefinition (m_parser->getSymbolTable ()->registerSymbol (fileName), lib);
            }
        }
    }
  
}

void SVLibShapeListener::enterInclude_statement(SV3_1aParser::Include_statementContext * ctx) {
  std::string filePath = ctx->file_path_spec ()->getText();
  
  std::pair<int, int> lineCol = ParseUtils::getLineColumn (m_tokens, ctx);
  if (!FileUtils::fileExists (filePath))
    {
      Location loc (m_parser->getFileId (), lineCol.first, 0, m_parser->getSymbolTable()->registerSymbol (filePath)); 
      Error err(ErrorDefinition::PP_CANNOT_OPEN_INCLUDE_FILE, loc);
      m_parser->getErrorContainer ()->addError (err);
      return;
    }
  
  ParseLibraryDef parser(m_parser->getCommandLineParser (), m_parser->getErrorContainer (), 
                         m_parser->getSymbolTable (), 
                         m_parser->getLibrarySet (), m_parser->getConfigSet());
  parser.parseLibraryDefinition (m_parser->getSymbolTable ()->registerSymbol (filePath));
}


void SVLibShapeListener::enterUselib_directive(SV3_1aParser::Uselib_directiveContext *ctx) {
    
}
      
void SVLibShapeListener::enterConfig_declaration(SV3_1aParser::Config_declarationContext *ctx) {
    
}

void SVLibShapeListener::enterDesign_statement(SV3_1aParser::Design_statementContext *ctx) {
    
}

void SVLibShapeListener::enterConfig_rule_statement(SV3_1aParser::Config_rule_statementContext *ctx) {
}

void SVLibShapeListener::enterDefault_clause(SV3_1aParser::Default_clauseContext *ctx) {
    
}

void SVLibShapeListener::enterInst_clause(SV3_1aParser::Inst_clauseContext *ctx) {
    
}

void SVLibShapeListener::enterInst_name(SV3_1aParser::Inst_nameContext *ctx) {
    
}

void SVLibShapeListener::enterCell_clause(SV3_1aParser::Cell_clauseContext *ctx) {
    
}

void SVLibShapeListener::enterLiblist_clause(SV3_1aParser::Liblist_clauseContext *ctx) {
    
}

void SVLibShapeListener::enterUse_clause(SV3_1aParser::Use_clauseContext *ctx) {
    
}

