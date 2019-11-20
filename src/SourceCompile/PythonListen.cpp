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

/* parserAntlrHandler
 * File:   PythonListen.cpp
 * Author: alainparserAntlrHandler
 *
 * Created on June 4, 2017, 8:09 PM
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
using namespace std;
using namespace antlr4;
using namespace SURELOG;

#include "parser/SV3_1aLexer.h"
#include "parser/SV3_1aParser.h"
#include "parser/SV3_1aParserBaseListener.h"
#include "API/SV3_1aPythonListener.h"

#include "SourceCompile/PythonListen.h"
#include "Cache/PythonAPICache.h"

using namespace SURELOG;

PythonListen::PythonListen(ParseFile* parse,
                           CompileSourceFile* compileSourceFile)
    : m_parse(parse),
      m_compileSourceFile(compileSourceFile),
      m_usingCachedVersion(false) {}

PythonListen::PythonListen(const PythonListen& orig) {}

PythonListen::~PythonListen() {}

void PythonListen::addError(Error& error) {
  getCompileSourceFile()->getErrorContainer()->addError(error);
}

bool PythonListen::listen() {
  PythonAPICache cache(this);
  if (cache.restore()) {
    m_usingCachedVersion = true;
    return true;
  }

  // This is either a parent Parser object of this Parser object has no parent
  if ((m_parse->m_children.size() != 0) || (m_parse->m_parent == NULL)) {
    if ((m_parse->m_parent == NULL) && (m_parse->m_children.size() == 0)) {
      SV3_1aPythonListener* pythonListener =
          new SV3_1aPythonListener(this, m_compileSourceFile->getPythonInterp(),
                                   m_parse->m_antlrParserHandler->m_tokens, 0);
      m_pythonListeners.push_back(pythonListener);
      tree::ParseTreeWalker::DEFAULT.walk(
          pythonListener, m_parse->m_antlrParserHandler->m_tree);
    }

    if (m_parse->m_children.size() != 0) {
      for (unsigned int i = 0; i < m_parse->m_children.size(); i++) {
        if (m_parse->m_children[i]->m_antlrParserHandler) {
          // Only visit the chunks that got re-parsed
          // TODO: Incrementally regenerate the FileContent

          SV3_1aPythonListener* pythonListener = new SV3_1aPythonListener(
              this, m_compileSourceFile->getPythonInterp(),
              m_parse->m_children[i]->m_antlrParserHandler->m_tokens,
              m_parse->m_children[i]->m_offsetLine);
          m_pythonListeners.push_back(pythonListener);
          tree::ParseTreeWalker::DEFAULT.walk(
              pythonListener,
              m_parse->m_children[i]->m_antlrParserHandler->m_tree);
        }
      }
    }
  }

  if (!cache.save()) {
    return false;
  }

  return true;
}
