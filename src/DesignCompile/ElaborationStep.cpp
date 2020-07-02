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

using namespace SURELOG;

ElaborationStep::~ElaborationStep() {}

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

bool ElaborationStep::bindPortType_(Signal* signal,
        const FileContent* fC, NodeId id, Scope* scope,
        DesignComponent* parentComponent,
        ErrorDefinition::ErrorType errtype)
{
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
      if (def == NULL && type == NULL && (interfName != "logic") &&
              (interfName != "byte") && (interfName != "bit") &&
              (interfName != "new") && (interfName != "expect") &&
              (interfName != "var") && (interfName != "signed") &&
              (interfName != "unsigned") && (interfName != "do") &&
              (interfName != "final") && (interfName != "global") &&
              (interfName != "soft")) {
        Location loc(symbols->registerSymbol(fC->getFileName(id)),
                fC->Line(id), 0,
                symbols->registerSymbol(interfName));
        Error err(ErrorDefinition::COMP_UNDEFINED_TYPE, loc);
        errors->addError(err);
      }

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
    std::string interfName = signal->getInterfaceTypeName();
    std::string baseName = interfName;
    std::string modPort;
    if (strstr(interfName.c_str(),".")) {
      modPort = interfName;
      StringUtils::ltrim(modPort,'.');
      StringUtils::rtrim(baseName,'.');
    }

    DesignComponent* def = nullptr;
    const DataType* type = nullptr;

    const std::pair<FileCNodeId, DesignComponent*>* datatype =
            parentComponent->getNamedObject(interfName);
    if (datatype) {
      def = datatype->second;
    } else {
      std::string name = parentComponent->getName() + "::" + interfName;
      def = design->getClassDefinition(name);
    }
    if (def == NULL) {
      def = design->getComponentDefinition(libName + "@" + baseName);
      if (def) {
        ModuleDefinition* module = dynamic_cast<ModuleDefinition*> (def);
        if (module) {
            signal->setInterfaceDef(module);
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
      signal->setDataType(type);
    }
    if (signal->getType() != slNoType) {
      return true;
    }
    if (def == NULL && type == NULL && (interfName != "logic") &&
            (interfName != "byte") && (interfName != "bit") &&
            (interfName != "new") && (interfName != "expect") &&
            (interfName != "var") && (interfName != "signed") &&
            (interfName != "unsigned") && (interfName != "do") &&
            (interfName != "final") && (interfName != "global") &&
            (interfName != "soft")) {
      Location loc(symbols->registerSymbol(fC->getFileName(id)),
              fC->Line(id), 0,
              symbols->registerSymbol(interfName));
      Error err(ErrorDefinition::COMP_UNDEFINED_TYPE, loc);
      errors->addError(err);
    }
    break;
  }
  default:
    break;
  }
  return true;
}
