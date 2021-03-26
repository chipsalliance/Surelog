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
 * File:   CompileClass.cpp
 * Author: alain
 *
 * Created on June 7, 2018, 10:26 PM
 */
#include "SourceCompile/VObjectTypes.h"
#include "Design/VObject.h"
#include "Library/Library.h"
#include "Design/Signal.h"
#include "Design/FileContent.h"
#include "Design/ClockingBlock.h"
#include "SourceCompile/SymbolTable.h"
#include "ErrorReporting/Error.h"
#include "ErrorReporting/Location.h"
#include "ErrorReporting/Error.h"
#include "CommandLine/CommandLineParser.h"
#include "ErrorReporting/ErrorDefinition.h"
#include "ErrorReporting/ErrorContainer.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/ParseFile.h"
#include "SourceCompile/Compiler.h"
#include "DesignCompile/CompileDesign.h"
#include "Testbench/ClassDefinition.h"
#include "DesignCompile/CompileClass.h"
#include "headers/uhdm.h"

using namespace SURELOG;

int FunctorCompileClass::operator()() const {
  CompileClass* instance =
      new CompileClass(m_compileDesign, m_class, m_design, m_symbols, m_errors);
  instance->compile();
  delete instance;
  return true;
}

bool CompileClass::compile() {
  const FileContent* fC = m_class->m_fileContents[0];
  NodeId nodeId = m_class->m_nodeIds[0];

  std::string fileName = fC->getFileName(nodeId);
  if (strstr(fileName.c_str(), "/bin/sv/builtin.sv")) {
    fileName = "builtin.sv";
  }
  std::string fullName;
  
  std::vector<std::string> names;
  ClassDefinition* parent = m_class;
  DesignComponent* tmp_container = nullptr;
  while (parent) {
    tmp_container = parent->getContainer();
    names.push_back(parent->getName());
    parent = parent->m_parent;
  }
  if (tmp_container) {
    fullName = tmp_container->getName() + "::";
  }
  if (names.size()) {
    unsigned int index = names.size() -1;
    while(1) {
      fullName += names[index];
      if (index > 0) fullName += "::";
      if (index == 0) break;
      index--;
    }
  }

  if (m_class->m_uhdm_definition->VpiFullName().empty())
    m_class->m_uhdm_definition->VpiFullName(fullName);
  Location loc(m_symbols->registerSymbol(fileName),
               fC->Line(nodeId), 0,
               m_symbols->registerSymbol(fullName));

  Error err1(ErrorDefinition::COMP_COMPILE_CLASS, loc);
  ErrorContainer* errors = new ErrorContainer(m_symbols);
  errors->regiterCmdLine(
      m_compileDesign->getCompiler()->getCommandLineParser());
  errors->addError(err1);
  errors->printMessage(
      err1,
      m_compileDesign->getCompiler()->getCommandLineParser()->muteStdout());
  delete errors;
  if (fC->getSize() == 0) return true;

  
  NodeId classId = m_class->m_nodeIds[0];

  do {
    VObject current = fC->Object(classId);
    classId = current.m_parent;
  } while (classId && !(
    (fC->Type(classId) == VObjectType::slDescription) ||
    (fC->Type(classId) == VObjectType::slClass_item)
                      )
    );
  if (classId) {
    VObject current = fC->Object(classId);
    classId = current.m_child;
    if (fC->Type(classId) == VObjectType::slAttribute_instance){
      UHDM::VectorOfattribute* attributes =
        m_helper.compileAttributes(m_class, fC, classId, m_compileDesign);
      m_class->Attributes(attributes);
    }
  }
  

  // Package imports
  std::vector<FileCNodeId> pack_imports;
  // - Local file imports
  for (auto import : fC->getObjects(VObjectType::slPackage_import_item)) {
    pack_imports.push_back(import);
  }
  // - Parent container imports
  DesignComponent* container = m_class->getContainer();
  if (container) {
    // FileCNodeId itself(container->getFileContents ()[0],
    // container->getNodeIds ()[0]); pack_imports.push_back(itself);
    for (auto import :
         container->getObjects(VObjectType::slPackage_import_item)) {
      pack_imports.push_back(import);
    }
  }

  for (const auto& pack_import : pack_imports) {
    const FileContent* pack_fC = pack_import.fC;
    NodeId pack_id = pack_import.nodeId;
    m_helper.importPackage(m_class, m_design, pack_fC, pack_id, m_compileDesign);
  }

  compile_class_parameters_(fC, nodeId);

  // This
  DataType* thisdt =
      new DataType(fC, nodeId, "this", VObjectType::slClass_declaration);
  thisdt->setDefinition(m_class);
  Property* prop = new Property(thisdt, fC, nodeId, 0, "this", false, false,
                                false, false, false);
  m_class->insertProperty(prop);

  VObject current = fC->Object(fC->getSize() - 2);
  NodeId id = nodeId;
  if (!id) return false;
  std::stack<NodeId> stack;
  stack.push(id);
  bool inFunction_body_declaration = false;
  bool inTask_body_declaration = false;
  while (stack.size()) {
    bool skipGuts = false;
    id = stack.top();
    stack.pop();
    current = fC->Object(id);
    VObjectType type = fC->Type(id);
    switch (type) {
      case VObjectType::slPackage_import_item: {
        m_helper.importPackage(m_class, m_design, fC, id, m_compileDesign);
        m_helper.compileImportDeclaration(m_class, fC, id, m_compileDesign);
        break;
      }
      case VObjectType::slClass_constructor_declaration: {
        inFunction_body_declaration = true;
        break;
      }
      case VObjectType::slFunction_body_declaration: {
        inFunction_body_declaration = true;
        break;
      }
      case VObjectType::slEndfunction: {
        inFunction_body_declaration = false;
        break;
      }
      case VObjectType::slTask_body_declaration: {
        inTask_body_declaration = true;
        break;
      }
      case VObjectType::slEndtask: {
        inTask_body_declaration = false;
        break;
      }
      case VObjectType::slClass_property:
        if (inFunction_body_declaration || inTask_body_declaration) break;
        compile_class_property_(fC, id);
        break;
      case VObjectType::slClass_constraint:
        compile_class_constraint_(fC, id);
        break;
      case VObjectType::slClass_declaration:
        if (id != nodeId) {
          compile_class_declaration_(fC, id);
          if (current.m_sibling) 
            stack.push(current.m_sibling);
          continue;
        }
        break;
      case VObjectType::slCovergroup_declaration:
        compile_covergroup_declaration_(fC, id);
        break;
      case VObjectType::slLocal_parameter_declaration:
        compile_local_parameter_declaration_(fC, id);
        break;
      case VObjectType::slParameter_declaration:
        compile_parameter_declaration_(fC, id);
        break;
      case VObjectType::slClass_method:
        compile_class_method_(fC, id);
        skipGuts = true;
        break;
      case VObjectType::slClass_type:
        compile_class_type_(fC, id);
      default:
        break;
    }

    if (current.m_sibling) stack.push(current.m_sibling);
    if (!skipGuts)
      if (current.m_child) stack.push(current.m_child);
  }

  // Default constructor
  DataType* returnType = new DataType();
  FunctionMethod* method =
      new FunctionMethod(m_class, fC, nodeId, "new", returnType, false, false,
                         false, false, false, false);
  method->compile(m_helper);
  Function* prevDef = m_class->getFunction("new");
  if (!prevDef) {
    m_class->insertFunction(method);
  }

  return true;
}

bool CompileClass::compile_class_property_(const FileContent* fC, NodeId id) {

  NodeId data_declaration = fC->Child(id);
  m_helper.compileDataDeclaration(m_class, fC, data_declaration, false, m_compileDesign);

  NodeId var_decl = fC->Child(data_declaration);
  VObjectType type = fC->Type(data_declaration);
  bool is_local = false;
  bool is_static = false;
  bool is_protected = false;
  bool is_rand = false;
  bool is_randc = false;
  while ((type == VObjectType::slPropQualifier_ClassItem) ||
         (type == VObjectType::slPropQualifier_Rand) ||
         (type == VObjectType::slPropQualifier_Randc)) {
    NodeId qualifier = fC->Child(data_declaration);
    VObjectType qualType = fC->Type(qualifier);
    if (qualType == VObjectType::slClassItemQualifier_Protected)
      is_protected = true;
    if (qualType == VObjectType::slClassItemQualifier_Static) is_static = true;
    if (qualType == VObjectType::slClassItemQualifier_Local) is_local = true;
    if (type == VObjectType::slPropQualifier_Rand) is_rand = true;
    if (type == VObjectType::slPropQualifier_Randc) is_randc = true;
    data_declaration = fC->Sibling(data_declaration);
    type = fC->Type(data_declaration);
    var_decl = fC->Child(data_declaration);
  }

  if (type == VObjectType::slData_declaration) {
    /*
   n<A> u<3> t<StringConst> p<37> s<12> l<5>
   n<> u<4> t<IntegerAtomType_Int> p<5> l<6>
   n<> u<5> t<Data_type> p<9> c<4> s<8> l<6>
   n<size> u<6> t<StringConst> p<7> l<6>
   n<> u<7> t<Variable_decl_assignment> p<8> c<6> l<6>
   n<> u<8> t<List_of_variable_decl_assignments> p<9> c<7> l<6>
   n<> u<9> t<Variable_declaration> p<10> c<5> l<6>
   n<> u<10> t<Data_declaration> p<11> c<9> l<6>
   n<> u<11> t<Class_property> p<12> c<10> l<6>
   n<> u<12> t<Class_item> p<37> c<11> s<35> l<6>
     */
    VObjectType var_type = fC->Type(var_decl);
    if (var_type == VObjectType::slVariable_declaration) {
      NodeId data_type = fC->Child(var_decl);
      NodeId node_type = fC->Child(data_type);

      VObjectType the_type = fC->Type(node_type);
      std::string typeName;
      if (the_type == VObjectType::slStringConst) {
        typeName = fC->SymName(node_type);
      } else if (the_type == VObjectType::slClass_scope) {
        NodeId class_type = fC->Child(node_type);
        NodeId class_name = fC->Child(class_type);
        typeName = fC->SymName(class_name);
        typeName += "::";
        NodeId symb_id = fC->Sibling(node_type);
        typeName += fC->SymName(symb_id);
      } else {
        typeName = VObject::getTypeName(the_type);
      }
      DataType* datatype = m_class->getUsedDataType(typeName);
      if (!datatype) {
        DataType* type =
            new DataType(fC, node_type, typeName, fC->Type(node_type));
        m_class->insertUsedDataType(typeName, type);
        datatype = m_class->getUsedDataType(typeName);
      }

      NodeId list_of_variable_decl_assignments = fC->Sibling(data_type);
      NodeId variable_decl_assignment =
          fC->Child(list_of_variable_decl_assignments);
      while (variable_decl_assignment) {
        NodeId var = fC->Child(variable_decl_assignment);
        NodeId range = fC->Sibling(var);
        std::string varName = fC->SymName(var);

        Property* previous = m_class->getProperty(varName);
        if (previous) {
          Location loc1(m_symbols->registerSymbol(fC->getFileName(var)),
                        fC->Line(var), 0, m_symbols->registerSymbol(varName));
          const FileContent* prevFile = previous->getFileContent();
          NodeId prevNode = previous->getNodeId();
          Location loc2(
              m_symbols->registerSymbol(prevFile->getFileName(prevNode)),
              prevFile->Line(prevNode), 0, m_symbols->registerSymbol(varName));
          Error err(ErrorDefinition::COMP_MULTIPLY_DEFINED_PROPERTY, loc1,
                    loc2);
          m_errors->addError(err);
        }

        Property* prop =
            new Property(datatype, fC, var, range, varName, is_local, is_static,
                         is_protected, is_rand, is_randc);
        m_class->insertProperty(prop);

        variable_decl_assignment = fC->Sibling(variable_decl_assignment);
      }
    } 
  }

  return true;
}

bool CompileClass::compile_class_method_(const FileContent* fC, NodeId id) {
  /*
    n<> u<8> t<MethodQualifier_Virtual> p<21> s<20> l<12>
    n<> u<9> t<Function_data_type> p<10> l<12>
    n<> u<10> t<Function_data_type_or_implicit> p<19> c<9> s<11> l<12>
    n<print_tree1> u<11> t<StringConst> p<19> s<17> l<12>
    n<> u<12> t<IntegerAtomType_Int> p<13> l<12>
    n<> u<13> t<Data_type> p<14> c<12> l<12>
    n<> u<14> t<Data_type_or_implicit> p<16> c<13> s<15> l<12>
    n<a> u<15> t<StringConst> p<16> l<12>
    n<> u<16> t<Tf_port_item> p<17> c<14> l<12>
    n<> u<17> t<Tf_port_list> p<19> c<16> s<18> l<12>
    n<> u<18> t<Endfunction> p<19> l<14>
    n<> u<19> t<Function_body_declaration> p<20> c<10> l<12>
    n<> u<20> t<Function_declaration> p<21> c<19> l<12>
    n<> u<21> t<Class_method> p<22> c<8> l<12>
   */
  NodeId func_decl = fC->Child(id);
  VObjectType func_type = fC->Type(func_decl);
  std::string funcName;
  std::string taskName;
  bool is_virtual = false;
  bool is_extern = false;
  bool is_static = false;
  bool is_local = false;
  bool is_protected = false;
  bool is_pure = false;
  DataType* returnType = new DataType();
  while ((func_type == VObjectType::slMethodQualifier_Virtual) ||
         (func_type == VObjectType::slMethodQualifier_ClassItem) ||
         (func_type == VObjectType::slPure_virtual_qualifier) ||
         (func_type == VObjectType::slExtern_qualifier) ||
         (func_type == VObjectType::slClassItemQualifier_Protected)) {
    if (func_type == VObjectType::slMethodQualifier_Virtual) {
      is_virtual = true;
      func_decl = fC->Sibling(func_decl);
      func_type = fC->Type(func_decl);
    }
    if (func_type == VObjectType::slClassItemQualifier_Protected) {
      is_protected = true;
      func_decl = fC->Sibling(func_decl);
      func_type = fC->Type(func_decl);
    }
    if (func_type == VObjectType::slPure_virtual_qualifier) {
      is_virtual = true;
      is_pure = true;
      func_decl = fC->Sibling(func_decl);
      func_type = fC->Type(func_decl);
    }
    if (func_type == VObjectType::slExtern_qualifier) {
      is_extern = true;
      func_decl = fC->Sibling(func_decl);
      func_type = fC->Type(func_decl);
    }
    if (func_type == VObjectType::slMethodQualifier_ClassItem) {
      NodeId qualifier = fC->Child(func_decl);
      VObjectType type = fC->Type(qualifier);
      if (type == VObjectType::slClassItemQualifier_Static) is_static = true;
      if (type == VObjectType::slClassItemQualifier_Local) is_local = true;
      if (type == VObjectType::slClassItemQualifier_Protected)
        is_protected = true;
      func_decl = fC->Sibling(func_decl);
      func_type = fC->Type(func_decl);
    }
  }
  if (func_type == VObjectType::slFunction_declaration) {
    NodeId func_body_decl = fC->Child(func_decl);
    NodeId function_data_type_or_implicit = fC->Child(func_body_decl);
    NodeId function_data_type = fC->Child(function_data_type_or_implicit);
    NodeId data_type = fC->Child(function_data_type);
    NodeId type = fC->Child(data_type);
    VObjectType the_type = fC->Type(type);
    std::string typeName;
    if (the_type == VObjectType::slStringConst) {
      typeName = fC->SymName(type);
    } else {
      typeName = VObject::getTypeName(the_type);
    }
    returnType->init(fC, type, typeName, fC->Type(type));
    NodeId function_name = fC->Sibling(function_data_type_or_implicit);
    funcName = fC->SymName(function_name);

    m_helper.compileFunction(m_class, fC, fC->Child(id), m_compileDesign, true);
    m_helper.compileFunction(m_class, fC, fC->Child(id), m_compileDesign, true);

  } else if (func_type == VObjectType::slTask_declaration) {
    /*
     n<cfg_dut> u<143> t<StringConst> p<146> s<144> l<37>
     n<> u<144> t<Endtask> p<146> s<145> l<39>
     n<cfg_dut> u<145> t<StringConst> p<146> l<39>
     n<> u<146> t<Task_body_declaration> p<147> c<143> l<37>
     n<> u<147> t<Task_declaration> p<148> c<146> l<37>
     n<> u<148> t<Class_method> p<149> c<147> l<37>
     */
    NodeId task_body_decl = fC->Child(func_decl);
    NodeId task_name = fC->Child(task_body_decl);
    taskName = fC->SymName(task_name);
  
    m_helper.compileTask(m_class, fC, fC->Child(id), m_compileDesign, true);
    m_helper.compileTask(m_class, fC, fC->Child(id), m_compileDesign, true);

  } else if (func_type == VObjectType::slMethod_prototype) {
    /*
     n<> u<65> t<IntVec_TypeBit> p<66> l<37>
     n<> u<66> t<Data_type> p<67> c<65> l<37>
     n<> u<67> t<Function_data_type> p<69> c<66> s<68> l<37>
     n<is_active> u<68> t<StringConst> p<69> l<37>
     n<> u<69> t<Function_prototype> p<70> c<67> l<37>
     n<> u<70> t<Method_prototype> p<71> c<69> l<37>
     n<> u<71> t<Class_method> p<72> c<70> l<37>
     */
    NodeId func_prototype = fC->Child(func_decl);
    if (fC->Type(func_prototype) == VObjectType::slTask_prototype) {
      NodeId task_name = fC->Child(func_prototype);
      taskName = fC->SymName(task_name);

      m_helper.compileTask(m_class, fC, fC->Child(id), m_compileDesign, true);
      m_helper.compileTask(m_class, fC, fC->Child(id), m_compileDesign, true);

    } else {
      NodeId function_data_type = fC->Child(func_prototype);
      NodeId data_type = fC->Child(function_data_type);
      NodeId type = fC->Child(data_type);
      VObjectType the_type = fC->Type(type);
      std::string typeName;
      if (the_type == VObjectType::slStringConst) {
        typeName = fC->SymName(type);
      } else {
        typeName = VObject::getTypeName(the_type);
      }
      returnType->init(fC, type, typeName, fC->Type(type));
      NodeId function_name = fC->Sibling(function_data_type);
      funcName = fC->SymName(function_name);

      m_helper.compileFunction(m_class, fC, fC->Child(id), m_compileDesign, true);
      m_helper.compileFunction(m_class, fC, fC->Child(id), m_compileDesign, true);

    }
    is_extern = true;
  } else if (func_type == VObjectType::slClass_constructor_declaration) {
    funcName = "new";
    returnType->init(fC, 0, "void", VObjectType::slNoType);

    m_helper.compileClassConstructorDeclaration(m_class, fC, fC->Child(id), m_compileDesign);

  } else if (func_type == VObjectType::slClass_constructor_prototype) {
    funcName = "new";

    m_helper.compileFunction(m_class, fC, fC->Child(id), m_compileDesign, true);
    m_helper.compileFunction(m_class, fC, fC->Child(id), m_compileDesign, true);
    
  } else {
    funcName = "UNRECOGNIZED_METHOD_TYPE";
  }
  if (!taskName.empty()) {
    TaskMethod* method = new TaskMethod(m_class, fC, id, taskName, is_extern);
    method->compile(m_helper);
    TaskMethod* prevDef = m_class->getTask(taskName);
    if (prevDef) {
      Location loc1(m_symbols->registerSymbol(fC->getFileName(id)),
                    fC->Line(id), 0, m_symbols->registerSymbol(taskName));
      const FileContent* prevFile = prevDef->getFileContent();
      NodeId prevNode = prevDef->getNodeId();
      Location loc2(m_symbols->registerSymbol(prevFile->getFileName(prevNode)),
                    prevFile->Line(prevNode), 0,
                    m_symbols->registerSymbol(taskName));
      Error err(ErrorDefinition::COMP_MULTIPLY_DEFINED_TASK, loc1, loc2);
      m_errors->addError(err);
    }
    m_class->insertTask(method);
  } else {
    FunctionMethod* method = new FunctionMethod(
        m_class, fC, id, funcName, returnType, is_virtual, is_extern, is_static,
        is_local, is_protected, is_pure);
    Variable* variable = new Variable(returnType, fC, id, 0, funcName);
    method->addVariable(variable);
    method->compile(m_helper);
    Function* prevDef = m_class->getFunction(funcName);
    if (prevDef) {
      SymbolId funcSymbol = m_symbols->registerSymbol(funcName);
      Location loc1(m_symbols->registerSymbol(fC->getFileName(id)),
                    fC->Line(id), 0, funcSymbol);
      const FileContent* prevFile = prevDef->getFileContent();
      NodeId prevNode = prevDef->getNodeId();
      Location loc2(m_symbols->registerSymbol(prevFile->getFileName(prevNode)),
                    prevFile->Line(prevNode), 0,
                    funcSymbol);
      if (funcSymbol != 0) {
        Error err(ErrorDefinition::COMP_MULTIPLY_DEFINED_FUNCTION, loc1, loc2);
        m_errors->addError(err);
      }
    }
    m_class->insertFunction(method);
  }
  return true;
}

bool CompileClass::compile_class_constraint_(const FileContent* fC,
                                             NodeId class_constraint) {
  NodeId constraint_prototype = fC->Child(class_constraint);
  NodeId constraint_name = fC->Child(constraint_prototype);
  std::string constName = fC->SymName(constraint_name);
  Constraint* prevDef = m_class->getConstraint(constName);
  if (prevDef) {
    Location loc1(m_symbols->registerSymbol(fC->getFileName(class_constraint)),
                  fC->Line(class_constraint), 0,
                  m_symbols->registerSymbol(constName));
    const FileContent* prevFile = prevDef->getFileContent();
    NodeId prevNode = prevDef->getNodeId();
    Location loc2(m_symbols->registerSymbol(prevFile->getFileName(prevNode)),
                  prevFile->Line(prevNode), 0,
                  m_symbols->registerSymbol(constName));
    Error err(ErrorDefinition::COMP_MULTIPLY_DEFINED_CONSTRAINT, loc1, loc2);
    m_errors->addError(err);
  }
  Constraint* constraint = new Constraint(fC, class_constraint, constName);
  m_class->insertConstraint(constraint);

  return true;
}

bool CompileClass::compile_class_declaration_(const FileContent* fC,
                                              NodeId id) {
  UHDM::Serializer& s = m_compileDesign->getSerializer();
  NodeId class_name_id = fC->Child(id);
  bool virtualClass = false;
  if (fC->Type(class_name_id) == VObjectType::slVirtual) {
    class_name_id = fC->Sibling(class_name_id);
    virtualClass = true;
  }
  std::string class_name = fC->SymName(class_name_id);
  std::string full_class_name = m_class->m_uhdm_definition->VpiFullName() + "::" + class_name;
  ClassDefinition* prevDef = m_class->getClass(class_name);
  if (prevDef) {
    Location loc1(m_symbols->registerSymbol(fC->getFileName(class_name_id)),
                  fC->Line(class_name_id), 0,
                  m_symbols->registerSymbol(class_name));
    const FileContent* prevFile = prevDef->getFileContent();
    NodeId prevNode = prevDef->getNodeId();
    Location loc2(m_symbols->registerSymbol(prevFile->getFileName(prevNode)),
                  prevFile->Line(prevNode), 0,
                  m_symbols->registerSymbol(class_name));
    Error err(ErrorDefinition::COMP_MULTIPLY_DEFINED_INNER_CLASS, loc1, loc2);
    m_errors->addError(err);
  }
  UHDM::class_defn* defn = s.MakeClass_defn();
  defn->VpiVirtual(virtualClass);
  defn->VpiName(class_name);
  defn->VpiFullName(full_class_name);
  ClassDefinition* the_class =
      new ClassDefinition(class_name, m_class->getLibrary(),
                          m_class->getContainer(), fC, class_name_id, m_class, defn);
  m_class->insertClass(the_class);
  UHDM::class_defn* parent = m_class->getUhdmDefinition();
  defn->VpiParent(parent);
  UHDM::VectorOfscope* scopes = parent->Scopes();
  if (scopes == nullptr) {
    parent->Scopes(s.MakeScopeVec());
    scopes = parent->Scopes();
  }
  scopes->push_back(defn);

  CompileClass* instance = new CompileClass(m_compileDesign, the_class,
                                            m_design, m_symbols, m_errors);
  instance->compile();
  delete instance;

  return true;
}

bool CompileClass::compile_covergroup_declaration_(const FileContent* fC,
                                                   NodeId id) {
  NodeId covergroup_name = fC->Child(id);
  std::string covergroupName = fC->SymName(covergroup_name);
  CoverGroupDefinition* prevDef = m_class->getCoverGroup(covergroupName);
  if (prevDef) {
    Location loc1(m_symbols->registerSymbol(fC->getFileName(covergroup_name)),
                  fC->Line(covergroup_name), 0,
                  m_symbols->registerSymbol(covergroupName));
    const FileContent* prevFile = prevDef->getFileContent();
    NodeId prevNode = prevDef->getNodeId();
    Location loc2(m_symbols->registerSymbol(prevFile->getFileName(prevNode)),
                  prevFile->Line(prevNode), 0,
                  m_symbols->registerSymbol(covergroupName));
    Error err(ErrorDefinition::COMP_MULTIPLY_DEFINED_COVERGROUP, loc1, loc2);
    m_errors->addError(err);
  }
  CoverGroupDefinition* covergroup =
      new CoverGroupDefinition(fC, id, covergroupName);
  m_class->insertCoverGroup(covergroup);

  return true;
}

bool CompileClass::compile_local_parameter_declaration_(const FileContent* fC,
                                                        NodeId id) {
  /*
   n<> u<8> t<IntegerAtomType_Int> p<9> l<3>
   n<> u<9> t<Data_type> p<10> c<8> l<3>
   n<> u<10> t<Data_type_or_implicit> p<20> c<9> s<19> l<3>
   n<FOO> u<11> t<StringConst> p<18> s<17> l<3>
   n<3> u<12> t<IntConst> p<13> l<3>
   n<> u<13> t<Primary_literal> p<14> c<12> l<3>
   n<> u<14> t<Constant_primary> p<15> c<13> l<3>
   n<> u<15> t<Constant_expression> p<16> c<14> l<3>
   n<> u<16> t<Constant_mintypmax_expression> p<17> c<15> l<3>
   n<> u<17> t<Constant_param_expression> p<18> c<16> l<3>
   n<> u<18> t<Param_assignment> p<19> c<11> l<3>
   n<> u<19> t<List_of_param_assignments> p<20> c<18> l<3>
   n<> u<20> t<Local_parameter_declaration> p<21> c<10> l<3>
  */
  NodeId list_of_type_assignments = fC->Child(id);
  if (fC->Type(list_of_type_assignments) == slList_of_type_assignments ||
      fC->Type(list_of_type_assignments) == slType) {
    // Type param
    m_helper.compileParameterDeclaration(m_class, fC, list_of_type_assignments,
                                         m_compileDesign, true, nullptr, false, false, false);

  } else {
    m_helper.compileParameterDeclaration(m_class, fC, id, m_compileDesign,
                                         true, nullptr, false, false, false);
  }
  NodeId data_type_or_implicit = fC->Child(id);
  NodeId list_of_param_assignments = fC->Sibling(data_type_or_implicit);
  NodeId param_assignment = fC->Child(list_of_param_assignments);
  while (param_assignment) {
    NodeId var = fC->Child(param_assignment);
    std::string name = fC->SymName(var);
    const std::pair<FileCNodeId, DesignComponent*>* prevDef =
        m_class->getNamedObject(name);
    if (prevDef) {
      Location loc1(m_symbols->registerSymbol(fC->getFileName(var)),
                    fC->Line(var), 0, m_symbols->registerSymbol(name));
      const FileContent* prevFile = prevDef->first.fC;
      NodeId prevNode = prevDef->first.nodeId;
      Location loc2(m_symbols->registerSymbol(prevFile->getFileName(prevNode)),
                    prevFile->Line(prevNode), 0,
                    m_symbols->registerSymbol(name));
      Error err(ErrorDefinition::COMP_MULTIPLY_DEFINED_PARAMETER, loc1, loc2);
      m_errors->addError(err);
    }

    FileCNodeId fnid(fC, id);
    m_class->addObject(VObjectType::slLocal_parameter_declaration, fnid);
    m_class->addNamedObject(name, fnid, NULL);

    param_assignment = fC->Sibling(param_assignment);
  }
  return true;
}

bool CompileClass::compile_parameter_declaration_(const FileContent* fC,
                                                  NodeId id) {
  NodeId list_of_type_assignments = fC->Child(id);
  if (fC->Type(list_of_type_assignments) == slList_of_type_assignments ||
      fC->Type(list_of_type_assignments) == slType) {
    // Type param
    m_helper.compileParameterDeclaration(m_class, fC, list_of_type_assignments,
                                         m_compileDesign, false, nullptr, false, false, false);

  } else {
    m_helper.compileParameterDeclaration(m_class, fC, id, m_compileDesign,
                                         false, nullptr, false, false, false);
  }

  NodeId data_type_or_implicit = fC->Child(id);
  NodeId list_of_param_assignments = fC->Sibling(data_type_or_implicit);
  NodeId param_assignment = fC->Child(list_of_param_assignments);
  while (param_assignment) {
    NodeId var = fC->Child(param_assignment);
    std::string name = fC->SymName(var);
    const std::pair<FileCNodeId, DesignComponent*>* prevDef =
        m_class->getNamedObject(name);
    if (prevDef) {
      Location loc1(m_symbols->registerSymbol(fC->getFileName(var)),
                    fC->Line(var), 0, m_symbols->registerSymbol(name));
      const FileContent* prevFile = prevDef->first.fC;
      NodeId prevNode = prevDef->first.nodeId;
      Location loc2(m_symbols->registerSymbol(prevFile->getFileName(prevNode)),
                    prevFile->Line(prevNode), 0,
                    m_symbols->registerSymbol(name));
      Error err(ErrorDefinition::COMP_MULTIPLY_DEFINED_PARAMETER, loc1, loc2);
      m_errors->addError(err);
    }

    FileCNodeId fnid(fC, id);
    m_class->addObject(VObjectType::slLocal_parameter_declaration, fnid);
    m_class->addNamedObject(name, fnid, NULL);

    param_assignment = fC->Sibling(param_assignment);
  }
  return true;
}

bool CompileClass::compile_class_type_(const FileContent* fC, NodeId id) {
  UHDM::Serializer& s = m_compileDesign->getSerializer();
  NodeId parent = fC->Parent(id);
  VObjectType ptype = fC->Type(parent);
  if (ptype != VObjectType::slClass_declaration) return true;
  NodeId base_class_id = fC->Child(id);
  std::string base_class_name = fC->SymName(base_class_id);
  while (fC->Sibling(base_class_id) &&
         (fC->Type(fC->Sibling(base_class_id)) == VObjectType::slStringConst)) {
    base_class_id = fC->Sibling(base_class_id);
    base_class_name += "::" + fC->SymName(base_class_id);
  }
  // Insert base class placeholder
  // Will be bound in UVMElaboration step
  ClassDefinition* base_class =
      new ClassDefinition(base_class_name, m_class->getLibrary(),
                          m_class->getContainer(), fC, base_class_id, NULL, s.MakeClass_defn());
  m_class->insertBaseClass(base_class);

  return true;
}

bool CompileClass::compile_class_parameters_(const FileContent* fC, NodeId id) {
  /*
  n<all_c> u<1> t<StringConst> p<16> s<14> l<3>
  n<uvm_port_base> u<2> t<StringConst> p<12> s<8> l<7>
  n<IF> u<3> t<StringConst> p<6> s<5> l<7>
  n<uvm_void> u<4> t<StringConst> p<5> l<7>
  n<> u<5> t<Data_type> p<6> c<4> l<7>
  n<> u<6> t<List_of_type_assignments> p<7> c<3> l<7>
  n<> u<7> t<Parameter_port_declaration> p<8> c<6> l<7>
  n<> u<8> t<Parameter_port_list> p<12> c<7> s<10> l<7>
  n<IF> u<9> t<StringConst> p<10> l<7>
  n<> u<10> t<Class_type> p<12> c<9> s<11> l<7>
  n<> u<11> t<Endclass> p<12> l<8>
  n<> u<12> t<Class_declaration> p<13> c<2> l<7>

  or

  n<T1> u<3> t<StringConst> p<9> s<5> l<18>
  n<> u<4> t<IntegerAtomType_Int> p<5> l<18>
  n<> u<5> t<Data_type> p<9> c<4> s<6> l<18>
  n<T2> u<6> t<StringConst> p<9> s<8> l<18>
  n<T1> u<7> t<StringConst> p<8> l<18>
  n<> u<8> t<Data_type> p<9> c<7> l<18>
  n<> u<9> t<List_of_type_assignments> p<10> c<3> l<18>
  n<> u<10> t<Parameter_port_declaration> p<11> c<9> l<18>
  n<> u<11> t<Parameter_port_list> p<31> c<10> s<20> l<18>

  */
  UHDM::class_defn* defn = m_class->getUhdmDefinition();
 
  NodeId className = fC->Child(id);
  if (fC->Type(className) == slVirtual) {
    className = fC->Sibling(className);
    defn->VpiVirtual(true);
  }
  NodeId paramList = fC->Sibling(className);

  if (fC->Type(paramList) == VObjectType::slParameter_port_list) {
    NodeId parameter_port_declaration = fC->Child(paramList);
    while (parameter_port_declaration) {
      NodeId list_of_type_assignments = fC->Child(parameter_port_declaration);
      if (fC->Type(list_of_type_assignments) == slList_of_type_assignments ||
          fC->Type(list_of_type_assignments) == slType) {
        // Type param
        m_helper.compileParameterDeclaration(m_class, fC, list_of_type_assignments, m_compileDesign, false, nullptr, false, false, false);

      } else {
        // Regular param
        m_helper.compileParameterDeclaration(m_class, fC, list_of_type_assignments, m_compileDesign, false, nullptr, false, false, false);

      }
      parameter_port_declaration = fC->Sibling(parameter_port_declaration);
    }
  }
  return true;
}
