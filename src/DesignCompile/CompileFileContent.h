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
 * File:   CompileFileContent.h
 * Author: alain
 *
 * Created on March 28, 2018, 10:16 PM
 */

#ifndef COMPILEFILECONTENT_H
#define COMPILEFILECONTENT_H

#include "DesignCompile/CompileHelper.h"

namespace SURELOG {

struct FunctorCompileFileContent {
  FunctorCompileFileContent(CompileDesign* compiler, FileContent* file,
                            Design* design, SymbolTable* symbols,
                            ErrorContainer* errors)
      : m_compileDesign(compiler),
        m_fileContent(file),
        m_design(design),
        m_symbols(symbols),
        m_errors(errors) {}
  int operator()() const;

 private:
  CompileDesign* m_compileDesign;
  FileContent* m_fileContent;
  Design* m_design;
  SymbolTable* m_symbols;
  ErrorContainer* m_errors;
};

class CompileFileContent final {
public:
  CompileFileContent(CompileDesign* compiler, FileContent* file, Design* design,
                     SymbolTable* symbols, ErrorContainer* errors)
      : m_compileDesign(compiler),
        m_fileContent(file),
        m_design(design),
        m_symbols(symbols),
        m_errors(errors) {
    m_helper.seterrorReporting(errors, symbols);
  }

  bool compile();

private:
  CompileFileContent(const CompileFileContent&) = delete;

  bool collectObjects_();
  CompileDesign* const m_compileDesign;
  FileContent* const m_fileContent;
  Design* const m_design;
  SymbolTable* const m_symbols;
  ErrorContainer* const m_errors;

  CompileHelper m_helper;
};

}  // namespace SURELOG

#endif /* COMPILEFILECONTENT_H */
