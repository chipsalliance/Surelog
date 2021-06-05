/*
 Copyright 2021 Alain Dargelas

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
 * File:   ParserHarness.h
 * Author: alain
 *
 * Created on June 5, 2021, 10:00 AM
 */

#ifndef PARSERHARNESS_H
#define PARSERHARNESS_H

#include <string>

#include "Design/FileContent.h"
#include "ErrorReporting/Error.h"
#include "SourceCompile/AntlrParserHandler.h"
#include "SourceCompile/CompilationUnit.h"
#include "parser/SV3_1aLexer.h"
#include "parser/SV3_1aParser.h"

namespace SURELOG {

class SV3_1aTreeShapeListener;
class SV3_1aPythonListener;
class AntlrParserErrorListener;
class CompileSourceFile;

class ParserHarness {
 public:
  FileContent* parse(const std::string& content);

 public:
 private:
};

};  // namespace SURELOG

#endif /* PARSERHARNESS_H */
