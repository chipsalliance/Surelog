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
 * File:   ElaborationStep.cpp
 * Author: alain
 *
 * Created on July 12, 2017, 8:55 PM
 */

#include "SourceCompile/VObjectTypes.h"
#include "Design/VObject.h"
#include "Library/Library.h"
#include "Utils/StringUtils.h"
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
#include "DesignCompile/CompileDesign.h"
#include "Testbench/ClassDefinition.h"
#include "DesignCompile/ElaborationStep.h"
#include "Design/Enum.h"
#include "Design/Netlist.h"
#include "Design/Struct.h"
#include "Design/Union.h"
#include "Design/SimpleType.h"
#include "headers/uhdm.h"
#include "headers/Serializer.h"
#include "headers/ElaboratorListener.h"
#include "headers/clone_tree.h"

using namespace SURELOG;
using namespace UHDM;

ElaborationStep::ElaborationStep(CompileDesign* compileDesign)
    : m_compileDesign(compileDesign) {
  m_exprBuilder.seterrorReporting(
      m_compileDesign->getCompiler()->getErrorContainer(),
      m_compileDesign->getCompiler()->getSymbolTable());
  m_exprBuilder.setDesign(m_compileDesign->getCompiler()->getDesign());
  m_helper.seterrorReporting(
      m_compileDesign->getCompiler()->getErrorContainer(),
      m_compileDesign->getCompiler()->getSymbolTable());
  m_symbols = m_compileDesign->getCompiler()->getSymbolTable();
  m_errors = m_compileDesign->getCompiler()->getErrorContainer();
}

ElaborationStep::~ElaborationStep() {}

bool ElaborationStep::bindTypedefs_() {
  Compiler* compiler = m_compileDesign->getCompiler();
  ErrorContainer* errors = compiler->getErrorContainer();
  SymbolTable* symbols = compiler->getSymbolTable();
  Design* design = compiler->getDesign();
  Serializer& s = m_compileDesign->getSerializer();
  std::vector<std::pair<TypeDef*, DesignComponent*>> defs;
  std::map<std::string, typespec*> specs;
  for (auto file : design->getAllFileContents()) {
    FileContent* fC = file.second;
    for (auto typed : fC->getTypeDefMap()) {
      TypeDef* typd = typed.second;
      defs.emplace_back(typd, fC);
    }
  }

  for (auto package : design->getPackageDefinitions()) {
    Package* pack = package.second;
    for (auto typed : pack->getTypeDefMap()) {
      TypeDef* typd = typed.second;
      defs.emplace_back(typd, pack);
    }
  }

  for (auto module : design->getModuleDefinitions()) {
    ModuleDefinition* mod = module.second;
    for (auto typed : mod->getTypeDefMap()) {
      TypeDef* typd = typed.second;
      defs.emplace_back(typd, mod);
    }
  }

  for (auto program_def : design->getProgramDefinitions()) {
    Program* program = program_def.second;
    for (auto typed : program->getTypeDefMap()) {
      TypeDef* typd = typed.second;
      defs.emplace_back(typd, program);
    }
  }

  for (auto class_def : design->getClassDefinitions()) {
    ClassDefinition* classp = class_def.second;
    for (auto typed : classp->getTypeDefMap()) {
      TypeDef* typd = typed.second;
      defs.emplace_back(typd, classp);
    }
  }

  for (auto& defTuple : defs) {
    TypeDef* typd = defTuple.first;
    DesignComponent* comp = defTuple.second;
    const DataType* prevDef = typd->getDefinition();
    bool noTypespec = false;
    if (prevDef) {
      prevDef = prevDef->getActual();
      if (prevDef->getTypespec() == nullptr)
        noTypespec = true;
      else 
        specs.insert(std::make_pair(prevDef->getTypespec()->VpiName(), prevDef->getTypespec()));
    }

    if (noTypespec == true) {
      if (prevDef && prevDef->getCategory() == DataType::Category::DUMMY) {
        const DataType* def =
            bindTypeDef_(typd, comp, ErrorDefinition::NO_ERROR_MESSAGE);
        if (def && (typd != def)) {
          typd->setDefinition(def);
          typd->setDataType((DataType*)def);
          if (typespec* tps = def->getTypespec()) {
            ElaboratorListener listener(&s);
            typespec* tpclone =
                (typespec*)UHDM::clone_tree((any*)tps, s, &listener);
            typd->setTypespec(tpclone);
            tpclone->VpiName(typd->getName());
            tpclone->Typedef_alias(tps);
            specs.insert(std::make_pair(typd->getName(), tpclone));
          }
        }
      }
      if (typd->getTypespec() == nullptr) {
        UHDM::typespec* ts = m_helper.compileTypespec(
            defTuple.second, typd->getFileContent(), typd->getDefinitionNode(),
            m_compileDesign, nullptr, nullptr, true);
        if (ts) {
          ts->VpiName(typd->getName());
          specs.insert(std::make_pair(typd->getName(), ts));
        }
        typd->setTypespec(ts);
      }
    } else if (prevDef == NULL) {
      const DataType* def =
          bindTypeDef_(typd, comp, ErrorDefinition::NO_ERROR_MESSAGE);
      if (def && (typd != def)) {
        typd->setDefinition(def);
        typd->setDataType((DataType*)def);
        typd->setTypespec(nullptr);
        UHDM::typespec* ts = m_helper.compileTypespec(
            defTuple.second, typd->getFileContent(), typd->getDefinitionNode(),
            m_compileDesign, nullptr, nullptr, true);
        if (ts) {
          specs.insert(std::make_pair(typd->getName(), ts));
          ts->VpiName(typd->getName());
        }
        typd->setTypespec(ts);
      } else {
        if (prevDef == NULL) {
          const FileContent* fC = typd->getFileContent();
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
    if (typespec* tps = typd->getTypespec()) {
      for (any* var : comp->getLateTypedefBinding()) {
        const typespec* orig = nullptr;
        if (expr* ex = dynamic_cast<expr*>(var)) {
          orig = ex->Typespec();
        } else if (typespec_member* ex = dynamic_cast<typespec_member*>(var)) {
          orig = ex->Typespec();
        } else if (parameter* ex = dynamic_cast<parameter*>(var)) {
          orig = ex->Typespec();
        } else if (type_parameter* ex = dynamic_cast<type_parameter*>(var)) {
          orig = ex->Typespec();
        }
        if (orig->UhdmType() == uhdmunsupported_typespec) {
          const std::string& need = orig->VpiName();
          if (need == tps->VpiName()) {
            s.unsupported_typespecMaker.Erase((unsupported_typespec*) orig);
            if (expr* ex = dynamic_cast<expr*>(var)) {
              ex->Typespec(tps);
            } else if (typespec_member* ex = dynamic_cast<typespec_member*>(var)) {
              ex->Typespec(tps);
            } else if (parameter* ex = dynamic_cast<parameter*>(var)) {
              ex->Typespec(tps);
            } else if (type_parameter* ex =
                           dynamic_cast<type_parameter*>(var)) {
              ex->Typespec(tps);
            }
          }
        }
      }
    }
  }
  for (auto module : design->getPackageDefinitions()) {
    DesignComponent* comp = module.second;
    for (any* var : comp->getLateTypedefBinding()) {
      const typespec* orig = nullptr;
      if (expr* ex = dynamic_cast<expr*>(var)) {
        orig = ex->Typespec();
      } else if (typespec_member* ex = dynamic_cast<typespec_member*>(var)) {
        orig = ex->Typespec();
      } else if (parameter* ex = dynamic_cast<parameter*>(var)) {
        orig = ex->Typespec();
      } else if (type_parameter* ex = dynamic_cast<type_parameter*>(var)) {
        orig = ex->Typespec();
      } 
      if (orig->UhdmType() == uhdmunsupported_typespec) {
        const std::string& need = orig->VpiName();
        std::map<std::string, typespec*>::iterator itr = specs.find(need);
        if (itr != specs.end()) {
          typespec* tps = (*itr).second;
          s.unsupported_typespecMaker.Erase((unsupported_typespec*)orig);
          if (expr* ex = dynamic_cast<expr*>(var)) {
            ex->Typespec(tps);
          } else if (typespec_member* ex =
                         dynamic_cast<typespec_member*>(var)) {
            ex->Typespec(tps);
          } else if (parameter* ex = dynamic_cast<parameter*>(var)) {
            ex->Typespec(tps);
          } else if (type_parameter* ex = dynamic_cast<type_parameter*>(var)) {
            ex->Typespec(tps);
          }
        } else {
          int setBreakpointHere = 0;
          setBreakpointHere ++;
        }
      }
    }
  }
  for (auto module : design->getModuleDefinitions()) {
    DesignComponent* comp = module.second;
    for (any* var : comp->getLateTypedefBinding()) {
      const typespec* orig = nullptr;
      if (expr* ex = dynamic_cast<expr*>(var)) {
        orig = ex->Typespec();
      } else if (typespec_member* ex = dynamic_cast<typespec_member*>(var)) {
        orig = ex->Typespec();
      } else if (parameter* ex = dynamic_cast<parameter*>(var)) {
        orig = ex->Typespec();
      } else if (type_parameter* ex = dynamic_cast<type_parameter*>(var)) {
        orig = ex->Typespec();
      } 
      if (orig->UhdmType() == uhdmunsupported_typespec) {
        const std::string& need = orig->VpiName();
        std::map<std::string, typespec*>::iterator itr = specs.find(need);
        if (itr != specs.end()) {
          typespec* tps = (*itr).second;
          s.unsupported_typespecMaker.Erase((unsupported_typespec*)orig);
          if (expr* ex = dynamic_cast<expr*>(var)) {
            ex->Typespec(tps);
          } else if (typespec_member* ex =
                         dynamic_cast<typespec_member*>(var)) {
            ex->Typespec(tps);
          } else if (parameter* ex = dynamic_cast<parameter*>(var)) {
            ex->Typespec(tps);
          } else if (type_parameter* ex = dynamic_cast<type_parameter*>(var)) {
            ex->Typespec(tps);
          }
        } else {
          int setBreakpointHere = 0;
          setBreakpointHere ++;
        }
      }
    }
  }
  return true;
}



const DataType* ElaborationStep::bindTypeDef_(
  TypeDef* typd,
  const DesignComponent* parent,
  ErrorDefinition::ErrorType errtype) {
  Compiler* compiler = m_compileDesign->getCompiler();
  SymbolTable* symbols = compiler->getSymbolTable();
  NodeId defNode = typd->getDefinitionNode();
  const FileContent* fC = typd->getFileContent();
  VObjectType defType = fC->Type(defNode);
  std::string objName;
  if (defType == VObjectType::slStringConst) {
    objName = fC->SymName(defNode);
  } else if (defType == VObjectType::slClass_scope) {
    NodeId class_type = fC->Child(defNode);
    NodeId nameId = fC->Child(class_type);
    objName = fC->SymName(nameId) + "::" + fC->SymName(fC->Sibling(defNode));
  } else {
    objName = "NOT_A_VALID_TYPE_NAME";
    symbols->registerSymbol(objName);
  }

  const DataType* result = bindDataType_(objName, fC, defNode, parent, errtype);
  if (result != typd)
    return result;
  else
    return NULL;
}

const DataType* ElaborationStep::bindDataType_(
  const std::string& type_name,
  const FileContent* fC,
  NodeId id, const DesignComponent* parent,
  ErrorDefinition::ErrorType errtype) {
  Compiler* compiler = m_compileDesign->getCompiler();
  ErrorContainer* errors = compiler->getErrorContainer();
  SymbolTable* symbols = compiler->getSymbolTable();
  Design* design = compiler->getDesign();
  std::string libName = "work";
  if (parent->getFileContents().size()) {
    libName = parent->getFileContents()[0]->getLibrary()->getName();
  }
  ClassNameClassDefinitionMultiMap classes = design->getClassDefinitions();
  bool found = false;
  bool classFound = false;
  std::string class_in_lib = libName + "@" + type_name;
  ClassNameClassDefinitionMultiMap::iterator itr1 = classes.end();

  if (type_name == "signed") {
    return new DataType(fC, id, type_name, VObjectType::slSigning_Signed);
  } else if (type_name == "unsigned") {
    return new DataType(fC, id, type_name, VObjectType::slSigning_Unsigned);
  } else if (type_name == "logic") {
    return new DataType(fC, id, type_name, VObjectType::slIntVec_TypeLogic);
  } else if (type_name == "bit") {
    return new DataType(fC, id, type_name, VObjectType::slIntVec_TypeBit);
  } else if (type_name == "byte") {
    return new DataType(fC, id, type_name, VObjectType::slIntegerAtomType_Byte);
  }

  const DataType* result = nullptr;
  if ((result = parent->getDataType(type_name))) {
    found = true;
  }
  if (found == false) {
    itr1 = classes.find(class_in_lib);

    if (itr1 != classes.end()) {
      found = true;
      classFound = true;
    }
  }
  if (found == false) {
    itr1 = classes.find(type_name);

    if (itr1 != classes.end()) {
      found = true;
      classFound = true;
    }
  }
  if (found == false) {
    std::string class_in_class = parent->getName() + "::" + type_name;
    itr1 = classes.find(class_in_class);

    if (itr1 != classes.end()) {
      found = true;
      classFound = true;
    }
  }
  if (found == false) {
    if (parent->getParentScope()) {
      std::string class_in_own_package =
          ((DesignComponent*)parent->getParentScope())->getName() +
          "::" + type_name;
      itr1 = classes.find(class_in_own_package);
      if (itr1 != classes.end()) {
        found = true;
        classFound = true;
      }
    }
  }
  if (found == false) {
    for (const auto& package : parent->getAccessPackages()) {
      std::string class_in_package = package->getName() + "::" + type_name;
      itr1 = classes.find(class_in_package);
      if (itr1 != classes.end()) {
        found = true;
        classFound = true;
        break;
      }
      const DataType* dtype = package->getDataType(type_name);
      if (dtype) {
        found = true;
        result = dtype;
        break;
      }
    }
  }
  if (found == false) {
    const ClassDefinition* classDefinition = dynamic_cast<const ClassDefinition*>(parent);
    if (classDefinition) {
      if (classDefinition->getName() == type_name) {
        result = classDefinition;
        found = true;
      }
      if (found == false) {
        Parameter* param = classDefinition->getParameter(type_name);
        if (param) {
          found = true;
          result = param;
        }
      }
      if (found == false) {
        if ((result = classDefinition->getBaseDataType(type_name))) {
          found = true;
        }
      }
      if (found == false) {
        if (classDefinition->getContainer()) {
          const DataType* dtype =
              classDefinition->getContainer()->getDataType(type_name);
          if (dtype) {
            found = true;
            result = dtype;
          }
        }
      }
    }
  }
  if (found == false) {
    const TypeDef* def = parent->getTypeDef(type_name);
    if (def) {
      found = true;
      result = def;
    }
  }

  if (found == false) {
    auto res = parent->getNamedObject(type_name);
    if (res) {
      DesignComponent* comp = res->second;
      result = dynamic_cast<ClassDefinition*>(comp);
      if (result) found = true;
    }
  }
  if (found == false) {
    auto res = parent->getNamedObject(libName + "@" + type_name);
    if (res) {
      DesignComponent* comp = res->second;
      result = dynamic_cast<ClassDefinition*>(comp);
      if (result) found = true;
    }
  }
  if (found == false) {
    const char* sname = type_name.c_str();
    if (strstr(sname, "::")) {
      std::vector<std::string> args;
      StringUtils::tokenizeMulti(type_name, "::", args);
      std::string classOrPackageName = args[0];
      std::string the_type_name = args[1];
      itr1 = classes.find(libName + "@" + classOrPackageName);
      if (itr1 == classes.end()) {
        if (parent->getParentScope()) {
          std::string class_in_own_package =
              ((DesignComponent*)parent->getParentScope())->getName() +
              "::" + classOrPackageName;
          itr1 = classes.find(class_in_own_package);
        }
      }
      if (itr1 != classes.end()) {
        const DataType* dtype = (*itr1).second->getDataType(the_type_name);
        if (dtype) {
          result = dtype;
          found = true;
        }
      }
      if (found == false) {
        Package* pack = design->getPackage(classOrPackageName);
        if (pack) {
          const DataType* dtype = pack->getDataType(the_type_name);
          if (dtype) {
            result = dtype;
            found = true;
          }
          if (found == false) {
            dtype = pack->getDataType(type_name);
            if (dtype) {
              result = dtype;
              found = true;
            }
          }
          if (found == false) {
            dtype = pack->getClassDefinition(type_name);
            if (dtype) {
              result = dtype;
              found = true;
            }
          }
        }
      }
    }
  }

  if ((found == false) && (errtype != ErrorDefinition::NO_ERROR_MESSAGE)) {
    std::string fileName = fC->getFileName(id);
    unsigned int line = fC->Line(id);
    Location loc1(symbols->registerSymbol(fileName), line, 0,
                  symbols->registerSymbol(type_name));
    Location loc2(0, 0, 0, symbols->registerSymbol(parent->getName()));
    Error err1(errtype, loc1, loc2);
    errors->addError(err1);
  } else {
    if (classFound == true) {
      // Binding
      ClassDefinition* def = (*itr1).second;
      result = def;
    }
  }
  while (result && result->getDefinition()) {
    result = result->getDefinition();
  }

  return result;
}

Variable* ElaborationStep::bindVariable_(std::string var_name, Scope* scope,
                                         const FileContent* fC, NodeId id,
                                         const DesignComponent* parent,
                                         ErrorDefinition::ErrorType errtype,
                                         bool returnClassParam) {
  Compiler* compiler = m_compileDesign->getCompiler();
  ErrorContainer* errors = compiler->getErrorContainer();
  SymbolTable* symbols = compiler->getSymbolTable();
  Variable* result = NULL;

  const ClassDefinition* classDefinition = dynamic_cast<const ClassDefinition*>(parent);
  if (classDefinition) result = classDefinition->getProperty(var_name);

  if (result == NULL) {
    if (scope) {
      result = scope->getVariable(var_name);
    }
  }
  if ((result == NULL) && scope) {
    Scope* itr_scope = scope;
    while (itr_scope) {
      Procedure* proc = dynamic_cast<Procedure*>(itr_scope);
      if (proc) {
        for (auto param : proc->getParams()) {
          if (param->getName() == var_name) {
            result = param;
            break;
          }
        }
      }
      if (result) break;
      itr_scope = itr_scope->getParentScope();
    }
  }

  if (result == NULL && parent) {
    for (auto package : parent->getAccessPackages()) {
      Value* val = package->getValue(var_name);
      if (val) {
        break;
      }
    }
  }

  if ((result == NULL) && (errtype != ErrorDefinition::NO_ERROR_MESSAGE)) {
    std::string fileName = fC->getFileName(id);
    unsigned int line = fC->Line(id);
    Location loc1(symbols->registerSymbol(fileName), line, 0,
                  symbols->registerSymbol(var_name));
    Location loc2(0, 0, 0, symbols->registerSymbol(parent->getName()));
    Error err1(errtype, loc1, loc2);
    errors->addError(err1);
  }

  if (!returnClassParam) {
    // Class parameters datatype have no definition and are strings
    if (result) {
      const DataType* dtype = result->getDataType();
      if (dtype && !dtype->getDefinition()) {
        if (dtype->getType() == VObjectType::slStringConst) {
          result = NULL;
        }
      }
    }
  }

  return result;
}

Variable* ElaborationStep::locateVariable_(std::vector<std::string>& var_chain,
                                           const FileContent* fC, NodeId id,
                                           Scope* scope,
                                           DesignComponent* parentComponent,
                                           ErrorDefinition::ErrorType errtype) {
  Variable* the_obj = NULL;
  const DesignComponent* currentComponent = parentComponent;
  for (auto var : var_chain) {
    if (var == "this") {
    } else if (var == "super") {
      const ClassDefinition* classDefinition =
          dynamic_cast<const ClassDefinition*>(currentComponent);
      if (classDefinition) {
        currentComponent = NULL;
        for (const auto &cc : classDefinition->getBaseClassMap()) {
          currentComponent = dynamic_cast<const ClassDefinition*>(cc.second);
          var = "this";
          break;
        }
        if (currentComponent == NULL) {
          var = "super";
          currentComponent = parentComponent;
        }
      }
    }

    the_obj =
        bindVariable_(var, scope, fC, id, currentComponent, errtype, false);
    if (the_obj) {
      const DataType* dtype = the_obj->getDataType();
      while (dtype && dtype->getDefinition()) {
        dtype = dtype->getDefinition();
      }
      const ClassDefinition* tmpClass = dynamic_cast<const ClassDefinition*>(dtype);
      if (tmpClass) {
        currentComponent = tmpClass;
      }
    }
  }
  return the_obj;
}

Variable* ElaborationStep::locateStaticVariable_(
    std::vector<std::string>& var_chain, const FileContent* fC, NodeId id,
    Scope* scope, DesignComponent* parentComponent,
    ErrorDefinition::ErrorType errtype) {
  std::string name;
  for (unsigned int i = 0; i < var_chain.size(); i++) {
    name += var_chain[i];
    if (i < var_chain.size() - 1) name += "::";
  }
  std::map<std::string, Variable*>::iterator itr = m_staticVariables.find(name);
  if (itr != m_staticVariables.end()) return (*itr).second;
  Variable* result = NULL;
  Design* design = m_compileDesign->getCompiler()->getDesign();
  if (var_chain.size() > 0) {
    Package* package = design->getPackage(var_chain[0]);
    if (package) {
      if (var_chain.size() > 1) {
        ClassDefinition* classDefinition =
            package->getClassDefinition(var_chain[1]);
        if (classDefinition) {
          if (var_chain.size() == 2) {
            result = new Variable(
                classDefinition, classDefinition->getFileContent(),
                classDefinition->getNodeId(), 0, classDefinition->getName());
          }
          if (var_chain.size() == 3) {
            std::vector<std::string> tmp;
            tmp.push_back(var_chain[2]);
            result =
                locateVariable_(tmp, fC, id, scope, classDefinition, errtype);
          }
        }
      }
    }

    if (result == NULL) {
      ClassDefinition* classDefinition =
          design->getClassDefinition(var_chain[0]);
      if (classDefinition == NULL) {
        std::string name;
        if (parentComponent && parentComponent->getParentScope()) {
          name =
              ((DesignComponent*)parentComponent->getParentScope())->getName();
          name += "::" + var_chain[0];
          classDefinition = design->getClassDefinition(name);
        }
      }
      if (classDefinition) {
        if (var_chain.size() == 1)
          result = new Variable(
              classDefinition, classDefinition->getFileContent(),
              classDefinition->getNodeId(), 0, classDefinition->getName());
        if (var_chain.size() == 2) {
          std::vector<std::string> tmp;
          tmp.push_back(var_chain[1]);

          const DataType* dtype = bindDataType_(
            var_chain[1], fC, id,
            classDefinition,
            ErrorDefinition::NO_ERROR_MESSAGE);
          if (dtype) {
            result = new Variable(dtype, dtype->getFileContent(),
                                  dtype->getNodeId(), 0, dtype->getName());
          } else
            result =
                locateVariable_(tmp, fC, id, scope, classDefinition, errtype);
        }
      }
    }
  }
  if (result == NULL) {
    if (var_chain.size()) {
      const DataType* dtype =
          bindDataType_(var_chain[0], fC, id, parentComponent, errtype);
      if (dtype) {
        result = new Variable(dtype, dtype->getFileContent(),
                              dtype->getNodeId(), 0, dtype->getName());
      }
    }
  }
  m_staticVariables.insert(std::make_pair(name, result));
  return result;
}

void checkIfBuiltInTypeOrErrorOut(DesignComponent* def, const FileContent* fC, NodeId id, const DataType* type,
                                  const std::string& interfName, ErrorContainer* errors, SymbolTable* symbols) {
  if (def == NULL && type == NULL && (interfName != "logic") &&
      (interfName != "byte") && (interfName != "bit") &&
      (interfName != "new") && (interfName != "expect") &&
      (interfName != "var") && (interfName != "signed") &&
      (interfName != "unsigned") && (interfName != "do") &&
      (interfName != "final") && (interfName != "global") &&
      (interfName != "soft")) {
    Location loc(symbols->registerSymbol(fC->getFileName(id)), fC->Line(id), 0,
                 symbols->registerSymbol(interfName));
    Error err(ErrorDefinition::COMP_UNDEFINED_TYPE, loc);
    errors->addError(err);
  }
}

bool bindStructInPackage(Design* design, Signal* signal, 
                      const std::string& packageName, const std::string& structName) {
  Package* p = design->getPackage(packageName);
  if (p) {
    const DataType* dtype = p->getDataType(structName);
    if (dtype) {
      signal->setDataType(dtype);
      const DataType* actual = dtype->getActual();
      if (actual->getCategory() == DataType::Category::STRUCT) {
        Struct* st = (Struct*) actual;
        if (st->isNet()) {
          signal->setType(slNetType_Wire);
        }
      }
      return true;
    } else {
      const DataType* dtype =
          p->getClassDefinition(structName);
      if (dtype) {
        signal->setDataType(dtype);
        return true;
      }
    }
  }
  return false;
}

bool ElaborationStep::bindPortType_(Signal* signal,
        const FileContent* fC, NodeId id, Scope* scope,
        DesignComponent* parentComponent,
        ErrorDefinition::ErrorType errtype)
{
  if (signal->getDataType() || signal->getInterfaceDef() || signal->getModPort())
    return true;
  Compiler* compiler = m_compileDesign->getCompiler();
  ErrorContainer* errors = compiler->getErrorContainer();
  SymbolTable* symbols = compiler->getSymbolTable();
  Design* design = compiler->getDesign();
  std::string libName = fC->getLibrary()->getName();
  VObjectType type = fC->Type(id);
  switch (type) {
  case VObjectType::slPort:
    /*
      n<mem_if> u<3> t<StringConst> p<6> s<5> l<1>
      n<> u<4> t<Constant_bit_select> p<5> l<1>
      n<> u<5> t<Constant_select> p<6> c<4> l<1>
      n<> u<6> t<Port_reference> p<11> c<3> s<10> l<1>
      n<mif> u<7> t<StringConst> p<10> s<9> l<1>
      n<> u<8> t<Constant_bit_select> p<9> l<1>
      n<> u<9> t<Constant_select> p<10> c<8> l<1>
      n<> u<10> t<Port_reference> p<11> c<7> l<1>
      n<> u<11> t<Port_expression> p<12> c<6> l<1>
      n<> u<12> t<Port> p<13> c<11> l<1>
     */
  {
    NodeId Port_expression = fC->Child(id);
    if (Port_expression &&
            (fC->Type(Port_expression) == VObjectType::slPort_expression)) {
      NodeId if_type = fC->Child(Port_expression);
      if (fC->Type(if_type) == VObjectType::slPort_reference) {
        NodeId if_type_name_s = fC->Child(if_type);
        NodeId if_name = fC->Sibling(if_type);
        if (if_name) {
          std::string interfaceName =
                  libName + "@" + fC->SymName(if_type_name_s);
          ModuleDefinition* interface =
                  design->getModuleDefinition(interfaceName);
          if (interface) {
            signal->setInterfaceDef(interface);
          } else {
            Location loc(symbols->registerSymbol(
                    fC->getFileName(if_type_name_s)),
                    fC->Line(if_type_name_s), 0,
                    symbols->registerSymbol(interfaceName));
            Error err(ErrorDefinition::COMP_UNDEFINED_INTERFACE, loc);
            errors->addError(err);
          }
        }
      }
    }
    break;
  }
  case VObjectType::slInput_declaration:
  case VObjectType::slOutput_declaration:
  case VObjectType::slInout_declaration:
  {
    break;
  }
  case VObjectType::slPort_declaration:
  {
    /*
     n<Configuration> u<21> t<StringConst> p<22> l<7>
     n<> u<22> t<Interface_identifier> p<26> c<21> s<25> l<7>
     n<cfg> u<23> t<StringConst> p<24> l<7>
     n<> u<24> t<Interface_identifier> p<25> c<23> l<7>
     n<> u<25> t<List_of_interface_identifiers> p<26> c<24> l<7>
     n<> u<26> t<Interface_port_declaration> p<27> c<22> l<7>
     n<> u<27> t<Port_declaration> p<28> c<26> l<7>
     */
    NodeId subNode = fC->Child(id);
    VObjectType subType = fC->Type(subNode);
    switch (subType) {
    case VObjectType::slInterface_port_declaration:
    {
      NodeId interface_identifier = fC->Child(subNode);
      NodeId interfIdName = fC->Child(interface_identifier);
      std::string interfName = fC->SymName(interfIdName);

      DesignComponent* def = nullptr;
      const DataType* type = nullptr;

      const std::pair<FileCNodeId, DesignComponent*>* datatype =
              parentComponent->getNamedObject(interfName);
      if (!datatype) {
        def = design->getClassDefinition(parentComponent->getName() +
                "::" + interfName);
      }
      if (datatype) {
        def = datatype->second;
      }
      if (def == NULL) {
        def = design->getComponentDefinition(libName + "@" +
                interfName);
      }
      if (def == NULL) {
        type = parentComponent->getDataType(interfName);
      }
      checkIfBuiltInTypeOrErrorOut(def, fC, id, type, interfName, errors, symbols);
      break;
    }
    case VObjectType::slInput_declaration:
    case VObjectType::slOutput_declaration:
    case VObjectType::slInout_declaration:
    {
      break;
    }
    default:
      break;
    }
    break;
  }
  case slStringConst:
  {
    std::string interfName;
    if (signal->getInterfaceTypeNameId()) {
      interfName = signal->getInterfaceTypeName();
    } else {
      if (NodeId typespecId = signal->getTypeSpecId()) {
        if (fC->Type(typespecId) == slClass_scope) {
          NodeId Class_type = fC->Child(typespecId);
          NodeId Class_type_name = fC->Child(Class_type);
          NodeId Class_scope_name = fC->Sibling(typespecId);
          if (bindStructInPackage(design, signal, fC->SymName(Class_type_name), fC->SymName(Class_scope_name)))
            return true;
        } else if (fC->Type(typespecId) == slStringConst) {
          interfName = fC->SymName(typespecId);
        }
      }
    }  
    std::string baseName = interfName;
    std::string modPort;
    if (strstr(interfName.c_str(),".")) {
      modPort = interfName;
      StringUtils::ltrim(modPort,'.');
      StringUtils::rtrim(baseName,'.');
    } else if (strstr(interfName.c_str(),"::")) {
      std::vector<std::string> result;
      StringUtils::tokenizeMulti(interfName, "::", result);
      if (result.size() > 1) {
        const std::string& packName = result[0];
        const std::string& structName = result[1];
        if (bindStructInPackage(design, signal, packName, structName))
          return true;
      }
    }

    DesignComponent* def = nullptr;
    const DataType* type = nullptr;

    const std::pair<FileCNodeId, DesignComponent*>* datatype =
            parentComponent->getNamedObject(interfName);
    if (datatype) {
      def = datatype->second;
      DataType* dt = dynamic_cast<DataType*> (def);
      if (dt) {
        signal->setDataType(dt);
      }
    } else {
      std::string name = parentComponent->getName() + "::" + interfName;
      def = design->getClassDefinition(name);
      DataType* dt = dynamic_cast<DataType*> (def);
      if (dt) {
        signal->setDataType(dt);
      }
    }
    if (def == NULL) {
      def = design->getComponentDefinition(libName + "@" + baseName);
      if (def) {
        ModuleDefinition* module = dynamic_cast<ModuleDefinition*> (def);
        ClassDefinition* cl = dynamic_cast<ClassDefinition*>(def);
        if (module) {
          signal->setInterfaceDef(module);
        } else if (cl) {
          signal->setDataType(cl);
          return true;
        } else {
          def = NULL;
        }
        if (!modPort.empty()) {
          if (module) {
            if (ModPort* modport = module->getModPort(modPort)) {
              signal->setModPort(modport);
            } else {
              def = NULL;
            }
          }
        }
      }
    }
    if (def == NULL) {
      def = design->getComponentDefinition(libName + "@" + baseName);
      ClassDefinition * c = dynamic_cast<ClassDefinition*> (def);
      if (c) {
        Variable* var = new Variable(c, fC, signal->getNodeId(), 0, signal->getName());
        parentComponent->addVariable(var);
        return false;
      } else {
        def = NULL;
      }
    }
    if (def == NULL) {
      type = parentComponent->getDataType(interfName);
      if (type) {
        const DataType* def = type->getActual();
        DataType::Category cat = def->getCategory();
        if (cat == DataType::Category::SIMPLE_TYPEDEF) {
          VObjectType t = def->getType();
          if (t == slIntVec_TypeLogic) { // Make "net types" explicit (vs variable types) for elab.
            signal->setType(slIntVec_TypeLogic);
          } else if (t == slIntVec_TypeReg) {
            signal->setType(slIntVec_TypeReg);
          } else if (t == slNetType_Wire) {
            signal->setType(slNetType_Wire);
          } 
        } else if (cat == DataType::Category::REF) {
          // Should not arrive here, there should always be an actual definition
        }
        signal->setDataType(type);
      }
    }
    if (signal->getType() != slNoType) {
      return true;
    }
    if (def == NULL) {
      if (parentComponent->getParameters()) {
        for (auto param : *parentComponent->getParameters()) {
          if (param->UhdmType() == uhdmtype_parameter) {
            if (param->VpiName() == interfName) {
              Parameter* p = parentComponent->getParameter(interfName);
              type = p;
              signal->setDataType(type);
              break;
            }
          }
        }
      }
    }
    checkIfBuiltInTypeOrErrorOut(def, fC, id, type, interfName, errors, symbols);
    break;
  }
  default:
    break;
  }
  return true;
}

UHDM::expr* ElaborationStep::exprFromAssign_(DesignComponent* component, const FileContent* fC, NodeId id, 
                                             NodeId unpackedDimension, ModuleInstance* instance) {
  // Assignment section
  NodeId assignment = 0;
  NodeId Assign = fC->Sibling(id);
  if (Assign && (fC->Type(Assign) == slExpression)) {
    assignment = Assign;
  }
  if (unpackedDimension) {
    NodeId tmp = unpackedDimension;
    while ((fC->Type(tmp) == slUnpacked_dimension) ||
           (fC->Type(tmp) == slVariable_dimension)) {
      tmp = fC->Sibling(tmp);
    }
    if (tmp && (fC->Type(tmp) != slUnpacked_dimension) &&
        (fC->Type(tmp) != slVariable_dimension)) {
      assignment = tmp;
    }
  }

  NodeId expression = 0;
  if (assignment) {
    if (fC->Type(assignment) == slClass_new) {
      expression = assignment;
    } else {
      NodeId Primary = fC->Child(assignment);
      if (fC->Type(assignment) == slExpression) {
        Primary = assignment;
      }
      expression = Primary;
    }
  } else {
    expression = fC->Sibling(id);
    if (fC->Type(expression) != VObjectType::slExpression) expression = 0;
  }

  expr* exp = nullptr;
  if (expression) {
    exp = (expr*)m_helper.compileExpression(component, fC, expression,
                                            m_compileDesign, nullptr, instance);
  }
  return exp;
}

UHDM::typespec* ElaborationStep::elabTypeParameter_(DesignComponent* component, Parameter* sit, ModuleInstance* instance) {
  Serializer& s = m_compileDesign->getSerializer();
  UHDM::any* uparam = sit->getUhdmParam();
  UHDM::typespec* spec = nullptr;
  bool type_param = false;
  if (uparam->UhdmType() == uhdmtype_parameter) {
    spec = (typespec*)((type_parameter*)uparam)->Typespec();
    type_param = true;
  } else {
    spec = (typespec*)((parameter*)uparam)->Typespec();
  }

  const std::string& pname = sit->getName();
  for (Parameter* param : instance->getTypeParams()) {
    // Param override
    if (param->getName() == pname) {
      UHDM::any* uparam = param->getUhdmParam();
      UHDM::typespec* override_spec = nullptr;
      if (uparam == nullptr) {
        if (type_param) {
          type_parameter* tp = s.MakeType_parameter();
          tp->VpiName(pname);
          param->setUhdmParam(tp);
        } else {
          parameter* tp = s.MakeParameter();
          tp->VpiName(pname);
          param->setUhdmParam(tp);
        }
        uparam = param->getUhdmParam();
      }

      if (type_param)
        override_spec = (UHDM::typespec*)((type_parameter*)uparam)->Typespec();
      else
        override_spec = (UHDM::typespec*)((parameter*)uparam)->Typespec();

      if (override_spec == nullptr) {
        ModuleInstance* parent = instance;
        if (ModuleInstance* pinst = instance->getParent()) 
          parent = pinst;
        override_spec = m_helper.compileTypespec(
            component, param->getFileContent(), param->getNodeType(),
            m_compileDesign, nullptr, parent, true);
      }

      if (override_spec) {
        if (type_param)
          ((type_parameter*)uparam)->Typespec(override_spec);
        else
          ((parameter*)uparam)->Typespec(override_spec);
        spec = override_spec;
        spec->VpiParent(uparam);
      }
      break;
    }
  }
  return spec;
}

any* ElaborationStep::makeVar_(DesignComponent* component, Signal* sig, std::vector<UHDM::range*>* packedDimensions, int packedSize, 
                std::vector<UHDM::range*>* unpackedDimensions, int unpackedSize, ModuleInstance* instance, 
                UHDM::VectorOfvariables* vars, UHDM::expr* assignExp, UHDM::typespec* tps) {
  Serializer& s = m_compileDesign->getSerializer();
  const DataType* dtype = sig->getDataType();
  VObjectType subnettype = sig->getType();

  std::string signame = sig->getName();
  
  variables* obj = nullptr;

  if (dtype) {
    dtype = dtype->getActual();
    if (const Enum* en = dynamic_cast<const Enum*>(dtype)) {
      enum_var* stv = s.MakeEnum_var();
      stv->Typespec(en->getTypespec());
      obj = stv;
      stv->Expr(assignExp);
    } else if (const Struct* st = dynamic_cast<const Struct*>(dtype)) {
      struct_var* stv = s.MakeStruct_var();
      stv->Typespec(st->getTypespec());
      obj = stv;
      stv->Expr(assignExp);
    } else if (const Union* un = dynamic_cast<const Union*>(dtype)) {
      union_var* stv = s.MakeUnion_var();
      stv->Typespec(un->getTypespec());
      obj = stv;
      stv->Expr(assignExp);
    } else if (const SimpleType* sit = dynamic_cast<const SimpleType*>(dtype)) {
      UHDM::typespec* spec = sit->getTypespec();
      spec = m_helper.elabTypespec(component, spec, m_compileDesign, nullptr, instance);
      variables* var = m_helper.getSimpleVarFromTypespec(spec, packedDimensions, m_compileDesign);
      var->Expr(assignExp);
      var->VpiConstantVariable(sig->isConst());
      var->VpiSigned(sig->isSigned());
      var->VpiName(signame);
      var->Typespec(spec);
      obj = var;
    } else if (/*const ClassDefinition* cl = */dynamic_cast<const ClassDefinition*>(dtype)) {
      class_var* stv = s.MakeClass_var();
      stv->Typespec(tps);
      obj = stv;
      stv->Expr(assignExp);
    } else if (Parameter* sit = (Parameter*)dynamic_cast<const Parameter*>(dtype)) {
      UHDM::typespec* spec = elabTypeParameter_(component, sit, instance);
      
      variables* var = m_helper.getSimpleVarFromTypespec(spec, packedDimensions, m_compileDesign);
      var->Expr(assignExp);
      var->VpiConstantVariable(sig->isConst());
      var->VpiSigned(sig->isSigned());
      var->VpiName(signame);
      obj = var;
    }
  } else if (tps) {
    UHDM::UHDM_OBJECT_TYPE tpstype = tps->UhdmType();
    if (tpstype == uhdmstruct_typespec) {
      struct_var* stv = s.MakeStruct_var();
      stv->Typespec(tps);
      stv->VpiName(signame);
      obj = stv;
      stv->Expr(assignExp);
    } else if (tpstype == uhdmenum_typespec) {
      enum_var* stv = s.MakeEnum_var();
      stv->Typespec(tps);
      stv->VpiName(signame);
      obj = stv;
      stv->Expr(assignExp);
    } else if (tpstype == uhdmbit_typespec) {
      bit_var* stv = s.MakeBit_var();
      stv->Typespec(tps);
      stv->VpiName(signame);
      stv->Ranges(unpackedDimensions);
      obj = stv;
      stv->Expr(assignExp);
    } else if (tpstype == uhdmbyte_typespec) {
      byte_var* stv = s.MakeByte_var();
      stv->Typespec(tps);
      stv->VpiName(signame);
      obj = stv;
      stv->Expr(assignExp);
    } else if (tpstype == uhdmunion_typespec) {
      union_var* stv = s.MakeUnion_var();
      stv->Typespec(tps);
      stv->VpiName(signame);
      obj = stv;
      stv->Expr(assignExp);
    } else if (tpstype == uhdmclass_typespec) {
      class_var* stv = s.MakeClass_var();
      stv->Typespec(tps);
      stv->VpiName(signame);
      tps->VpiParent(stv);
      obj = stv;
      stv->Expr(assignExp);
    }
  }

  if (obj == nullptr) {
    variables* var = nullptr;
    if (subnettype == slIntegerAtomType_Shortint) {
      UHDM::short_int_var* int_var = s.MakeShort_int_var();
      var = int_var;
    } else if (subnettype == slIntegerAtomType_Int) {
      UHDM::int_var* int_var = s.MakeInt_var();
      var = int_var;
    } else if (subnettype == slIntegerAtomType_LongInt) {
      UHDM::long_int_var* int_var = s.MakeLong_int_var();
      var = int_var;
    } else if (subnettype == slIntegerAtomType_Time) {
      UHDM::time_var* int_var = s.MakeTime_var();
      var = int_var;
    } else if (subnettype == slIntVec_TypeBit) {
      UHDM::bit_var* int_var = s.MakeBit_var();
      var = int_var;
    } else if (subnettype == slIntegerAtomType_Byte) {
      UHDM::byte_var* int_var = s.MakeByte_var();
      var = int_var;
    } else if (subnettype == slNonIntType_ShortReal) {
      UHDM::short_real_var* int_var = s.MakeShort_real_var();
      var = int_var;
    } else if (subnettype == slNonIntType_Real) {
      UHDM::real_var* int_var = s.MakeReal_var();
      var = int_var;
    } else if (subnettype == slNonIntType_RealTime) {
      UHDM::time_var* int_var = s.MakeTime_var();
      var = int_var;
    } else if (subnettype == slString_type) {
      UHDM::string_var* int_var = s.MakeString_var();
      var = int_var;
    } else {
      // default type (fallback)
      logic_var* logicv = s.MakeLogic_var();
      logicv->Ranges(packedDimensions);
      var = logicv;
    }
    var->VpiSigned(sig->isSigned());
    var->VpiConstantVariable(sig->isConst());
    var->VpiName(signame);
    var->Expr(assignExp);
    obj = var;
  } else if (packedDimensions) {
    // packed struct array ...
    UHDM::packed_array_var* parray = s.MakePacked_array_var();
    parray->Ranges(packedDimensions);
    VectorOfany* elements = s.MakeAnyVec();
    parray->Elements(elements);
    elements->push_back(obj);
    obj->VpiParent(parray);
    parray->VpiName(signame);
    obj = parray;
  }

  if (unpackedDimensions) {
    array_var* array_var = s.MakeArray_var();
    array_var->Variables(s.MakeVariablesVec());
    array_var->Ranges(unpackedDimensions);
    array_var->VpiSize(unpackedSize);
    array_var->VpiName(signame);
    array_var->VpiArrayType(vpiStaticArray);
    array_var->VpiRandType(vpiNotRand);
    array_var->VpiVisibility(vpiPublicVis);
    vars->push_back(array_var);
    obj->VpiParent(array_var);
    UHDM::VectorOfvariables* array_vars = array_var->Variables();
    array_vars->push_back((variables*)obj);
    array_var->Expr(assignExp);
  } else {
    if (obj->UhdmType() == uhdmenum_var) {
      ((enum_var*)obj)->VpiName(signame);
    } else if (obj->UhdmType() == uhdmstruct_var) {
      ((struct_var*)obj)->VpiName(signame);
    } else if (obj->UhdmType() == uhdmunion_var) {
      ((union_var*)obj)->VpiName(signame);
    } else if (obj->UhdmType() == uhdmclass_var) {
      ((class_var*)obj)->VpiName(signame);
    }
    vars->push_back((variables*)obj);
  }

  if (obj) {
    obj->VpiSigned(sig->isSigned());
    obj->VpiConstantVariable(sig->isConst());
    obj->VpiIsRandomized(sig->isRand() || sig->isRandc());
    if (sig->isRand())
      obj->VpiRandType(vpiRand);
    else if (sig->isRandc())
      obj->VpiRandType(vpiRandC);
    if (sig->isStatic()) {
      obj->VpiAutomatic(false);
    } else { 
      obj->VpiAutomatic(true);
    }
    if (sig->isProtected()) {
      obj->VpiVisibility(vpiProtectedVis);
    } else if (sig->isLocal()) {
      obj->VpiVisibility(vpiLocalVis);
    } else {
      obj->VpiVisibility(vpiPublicVis);
    }      
  }
  return obj;
}

