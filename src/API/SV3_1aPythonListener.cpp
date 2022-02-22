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
 * File:   SV3_1aPythonListener.cpp
 * Author: alain
 *
 * Created on April 16, 2017, 8:28 PM
 */

#include <Surelog/API/SV3_1aPythonListener.h>
#include <Surelog/ErrorReporting/ErrorContainer.h>
#include <Surelog/SourceCompile/PythonListen.h>
#include <Surelog/SourceCompile/SymbolTable.h>
#include <Surelog/Utils/ParseUtils.h>

namespace SURELOG {
SV3_1aPythonListener::SV3_1aPythonListener(PythonListen* pl,
                                           PyThreadState* interpState,
                                           antlr4::CommonTokenStream* tokens,
                                           unsigned int lineOffset)
    : m_pl(pl),
      m_interpState(interpState),
      m_tokens(tokens),
      m_lineOffset(lineOffset) {}

SV3_1aPythonListener::SV3_1aPythonListener(const SV3_1aPythonListener& orig) {}

SV3_1aPythonListener::~SV3_1aPythonListener() {}

void SV3_1aPythonListener::logError(ErrorDefinition::ErrorType error,
                                    antlr4::ParserRuleContext* ctx,
                                    std::string object, bool printColumn) {
  std::pair<int, int> lineCol =
      ParseUtils::getLineColumn(getTokenStream(), ctx);

  Location loc(
      m_pl->getParseFile()->getFileId(lineCol.first + m_lineOffset),
      m_pl->getParseFile()->getLineNb(lineCol.first + m_lineOffset),
      printColumn ? lineCol.second : 0,
      m_pl->getCompileSourceFile()->getSymbolTable()->registerSymbol(object));
  Error err(error, loc);
  m_pl->addError(err);
}

void SV3_1aPythonListener::logError(ErrorDefinition::ErrorType error,
                                    Location& loc, bool showDuplicates) {
  Error err(error, loc);
  m_pl->getCompileSourceFile()->getErrorContainer()->addError(err,
                                                              showDuplicates);
}

void SV3_1aPythonListener::logError(ErrorDefinition::ErrorType error,
                                    Location& loc, Location& extraLoc,
                                    bool showDuplicates) {
  std::vector<Location> extras;
  extras.push_back(extraLoc);
  Error err(error, loc, &extras);
  m_pl->getCompileSourceFile()->getErrorContainer()->addError(err,
                                                              showDuplicates);
}
}  // namespace SURELOG
