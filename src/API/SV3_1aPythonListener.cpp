/*
 * Copyright 2017 ACE Cloud LLC
 * This file is the sole propriety of ACE Cloud LLC
 * Use/modify only with explicit written authorization of ACE Cloud LLC 
 *  Alain Dargelas, President  * 
 */

/* 
 * File:   SV3_1aPythonListener.cpp
 * Author: alain
 * 
 * Created on April 16, 2017, 8:28 PM
 */
#include "../SourceCompile/SymbolTable.h"
#include "../CommandLine/CommandLineParser.hpp"
#include "../ErrorReporting/ErrorContainer.h"
#include "../SourceCompile/CompilationUnit.h"
#include "../SourceCompile/PreprocessFile.h"
#include "../SourceCompile/CompileSourceFile.h"
#include "../SourceCompile/Compiler.h"
#include "../SourceCompile/ParseFile.h"
#include "../SourceCompile/PythonListen.h"
#include <cstdlib>
#include <iostream>
#include "antlr4-runtime.h"
using namespace std;
using namespace antlr4;
using namespace SURELOG;

#include "../parser/SV3_1aLexer.h"
#include "../parser/SV3_1aParser.h"
#include "../parser/SV3_1aParserBaseListener.h"
#include "SV3_1aPythonListener.h"
using namespace antlr4;
#include "../Utils/ParseUtils.h"
#include "../Utils/FileUtils.h"
#include "PythonAPI.h"

SV3_1aPythonListener::SV3_1aPythonListener (PythonListen* pl, PyThreadState* interpState, antlr4::CommonTokenStream* tokens, unsigned int lineOffset) : 
m_pl(pl), m_interpState(interpState), m_tokens(tokens), m_lineOffset(lineOffset) { }

SV3_1aPythonListener::SV3_1aPythonListener (const SV3_1aPythonListener& orig) { }

SV3_1aPythonListener::~SV3_1aPythonListener () { }

void
SV3_1aPythonListener::logError (ErrorDefinition::ErrorType error, ParserRuleContext* ctx, std::string object, bool printColumn)
{
  std::pair<int, int> lineCol = ParseUtils::getLineColumn (getTokenStream (), ctx);

  Location loc (m_pl->getParseFile()->getFileId (lineCol.first + m_lineOffset), m_pl->getParseFile()->getLineNb (lineCol.first + m_lineOffset), printColumn ? lineCol.second : 0,
                m_pl->getCompileSourceFile()->getSymbolTable ()->registerSymbol(object));
  Error err (error, loc);
  m_pl->addError (err);

}

void
SV3_1aPythonListener::logError (ErrorDefinition::ErrorType error, Location& loc, bool showDuplicates)
{
  Error err (error, loc);
  m_pl->getCompileSourceFile ()->getErrorContainer ()->addError (err, showDuplicates);
}

void
SV3_1aPythonListener::logError (ErrorDefinition::ErrorType error, Location& loc, Location& extraLoc, bool showDuplicates)
{
  std::vector<Location> extras;
  extras.push_back (extraLoc);
  Error err (error, loc, &extras);
  m_pl->getCompileSourceFile ()->getErrorContainer ()->addError (err, showDuplicates);
}

