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
 * File:   PackageAndRootElaboration.cpp
 * Author: alain
 *
 * Created on June 3, 2019, 10:02 PM
 */

#include "SourceCompile/VObjectTypes.h"
#include "Design/VObject.h"
#include "Library/Library.h"
#include "Design/FileContent.h"
#include "SourceCompile/SymbolTable.h"
#include "ErrorReporting/Error.h"
#include "ErrorReporting/Location.h"
#include "ErrorReporting/Error.h"
#include "ErrorReporting/ErrorDefinition.h"
#include "ErrorReporting/ErrorContainer.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/ParseFile.h"
#include "SourceCompile/Compiler.h"
#include "CompileDesign.h"
#include "Testbench/Property.h"
#include "Design/Function.h"
#include "Testbench/ClassDefinition.h"
#include "PackageAndRootElaboration.h"

using namespace SURELOG;

PackageAndRootElaboration::~PackageAndRootElaboration() {}

bool PackageAndRootElaboration::elaborate() {
  bool result = true;
  result &= bindTypedefs_();
  return result;
}

bool PackageAndRootElaboration::bindTypedefs_() {
  Compiler* compiler = m_compileDesign->getCompiler();
  ErrorContainer* errors = compiler->getErrorContainer();
  SymbolTable* symbols = compiler->getSymbolTable();
  Design* design = compiler->getDesign();

  std::vector<std::pair<TypeDef*, DesignComponent*>> defs;

  for (auto file : design->getAllFileContents()) {
    FileContent* fC = file.second;
    for (auto typed : fC->getTypeDefMap()) {
      TypeDef* typd = typed.second;
      defs.push_back(std::make_pair(typd, fC));
    }
  }

  for (auto package : design->getPackageDefinitions()) {
    Package* pack = package.second;
    for (auto typed : pack->getTypeDefMap()) {
      TypeDef* typd = typed.second;
      defs.push_back(std::make_pair(typd, pack));
    }
  }

  for (auto program_def : design->getProgramDefinitions()) {
    Program* program = program_def.second;
    for (auto typed : program->getTypeDefMap()) {
      TypeDef* typd = typed.second;
      defs.push_back(std::make_pair(typd, program));
    }
  }

  for (auto def : defs) {
    TypeDef* typd = def.first;
    DesignComponent* comp = def.second;
    if (typd->getDefinition() == NULL) {
      DataType* def =
          bindTypeDef_(typd, comp, ErrorDefinition::NO_ERROR_MESSAGE);
      if (def) {
        typd->setDefinition(def);
      } else {
        FileContent* fC = typd->getFileContent();
        NodeId id = typd->getNodeId();
        std::string fileName = fC->getFileName(id);
        unsigned int line = fC->Line(id);
        std::string definition_string;
        NodeId defNode = typd->getDefinitionNode();
        VObjectType defType = fC->Type(defNode);
        if (defType == VObjectType::slStringConst) {
          definition_string = fC->SymName(defNode);
        }
        Location loc1(symbols->registerSymbol(fileName), line, 0,
                      symbols->registerSymbol(definition_string));
        Error err1(ErrorDefinition::COMP_UNDEFINED_TYPE, loc1);
        errors->addError(err1);
      }
    }
  }

  return true;
}
