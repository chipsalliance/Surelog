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
 * File:   TestbenchElaboration.cpp
 * Author: alain
 *
 * Created on February 6, 2019, 9:01 PM
 */

#include <Surelog/Common/FileSystem.h>
#include <Surelog/Design/Design.h>
#include <Surelog/Design/FileContent.h>
#include <Surelog/Design/Parameter.h>
#include <Surelog/Design/Signal.h>
#include <Surelog/Design/Statement.h>
#include <Surelog/Design/TfPortItem.h>
#include <Surelog/DesignCompile/CompileDesign.h>
#include <Surelog/DesignCompile/TestbenchElaboration.h>
#include <Surelog/SourceCompile/Compiler.h>
#include <Surelog/SourceCompile/SymbolTable.h>
#include <Surelog/Testbench/ClassDefinition.h>
#include <Surelog/Testbench/Property.h>
#include <Surelog/Utils/StringUtils.h>

// UHDM
#include <uhdm/class_defn.h>
#include <uhdm/class_typespec.h>
#include <uhdm/extends.h>

#include <queue>

namespace SURELOG {

bool checkValidFunction(const DataType* dtype, std::string_view function,
                        Statement* stmt, Design* design,
                        std::string& datatypeName) {
  bool validFunction = true;
  VObjectType type = dtype->getType();
  const DataType* def = dtype->getDefinition();
  if (type == VObjectType::paClass_declaration) {
    const ClassDefinition* the_class =
        datatype_cast<const ClassDefinition*>(dtype);
    if (the_class) {
      Function* func = the_class->getFunction(function);
      if (func)
        stmt->setFunction(func);
      else
        validFunction = false;
    } else {
      the_class = datatype_cast<const ClassDefinition*>(def);
      if (the_class) {
        Function* func = the_class->getFunction(function);
        if (func)
          stmt->setFunction(func);
        else
          validFunction = false;
        ClassDefinition* genClass =
            design->getClassDefinition("builtin::any_sverilog_class");
        if (genClass && genClass->getFunction(function)) {
          validFunction = true;
          stmt->setFunction(genClass->getFunction(function));
        }
      }
    }
  } else if (DataType::isString_type(type)) {
    ClassDefinition* array = design->getClassDefinition("builtin::string");
    if (array) {
      Function* func = array->getFunction(function);
      if (func)
        stmt->setFunction(func);
      else {
        datatypeName = "string";
        validFunction = false;
      }
    } else
      validFunction = false;
  } else
    validFunction = false;
  return validFunction;
}

bool checkValidBuiltinClass_(std::string_view classname,
                             std::string_view function, Statement* stmt,
                             Design* design, std::string& datatypeName) {
  bool validFunction = true;
  ClassDefinition* array =
      design->getClassDefinition(StrCat("builtin::", classname));
  if (array == nullptr) return false;
  Function* func = array->getFunction(function);
  if (func)
    stmt->setFunction(func);
  else {
    datatypeName = classname;
    validFunction = false;
  }
  return validFunction;
}

std::vector<std::string_view> computeVarChain(const FileContent* fC,
                                              NodeId nodeId) {
  std::vector<std::string_view> var_chain;
  while (nodeId) {
    VObjectType type = fC->Type(nodeId);
    switch (type) {
      case VObjectType::slStringConst: {
        var_chain.emplace_back(fC->SymName(nodeId));
        break;
      }
      case VObjectType::paImplicit_class_handle: {
        NodeId child = fC->Child(nodeId);
        VObjectType childType = fC->Type(child);
        if (childType == VObjectType::paThis_keyword)
          var_chain.emplace_back("this");
        else if (childType == VObjectType::paSuper_keyword)
          var_chain.emplace_back("super");
        else
          var_chain.emplace_back("UNKNOWN_TYPE");
        break;
      }
      default:
        var_chain.emplace_back("UNKNOWN_NAME");
        break;
    }
    nodeId = fC->Sibling(nodeId);
  }
  return var_chain;
}

bool TestbenchElaboration::bindClasses_() {
  checkForMultipleDefinition_();
  bindBaseClasses_();
  bindDataTypes_();
  bindFunctions_();
  bindTasks_();
  bindProperties_();
  return true;
}

bool TestbenchElaboration::checkForMultipleDefinition_() {
  FileSystem* const fileSystem = FileSystem::getInstance();
  Compiler* compiler = m_compileDesign->getCompiler();
  ErrorContainer* errors = compiler->getErrorContainer();
  SymbolTable* symbols = compiler->getSymbolTable();
  Design* design = compiler->getDesign();
  ClassNameClassDefinitionMultiMap classes = design->getClassDefinitions();

  // Check for multiple definition
  std::string prevClassName;
  ClassDefinition* prevClassDefinition = nullptr;
  for (ClassNameClassDefinitionMultiMap::iterator itr = classes.begin();
       itr != classes.end(); itr++) {
    std::string className = (*itr).first;
    ClassDefinition* classDefinition = (*itr).second;
    bool done = false;
    if (className == prevClassName) {
      const FileContent* fC1 = classDefinition->getFileContents()[0];
      NodeId nodeId1 = classDefinition->getNodeIds()[0];
      PathId fileId1 = fileSystem->copy(fC1->getFileId(nodeId1), symbols);
      uint32_t line1 = fC1->Line(nodeId1);
      Location loc1(fileId1, line1, fC1->Column(nodeId1),
                    symbols->registerSymbol(className));

      std::vector<Location> locations;

      while (1) {
        const FileContent* fC2 = prevClassDefinition->getFileContents()[0];
        NodeId nodeId2 = prevClassDefinition->getNodeIds()[0];
        PathId fileId2 = fileSystem->copy(fC2->getFileId(nodeId2), symbols);
        uint32_t line2 = fC2->Line(nodeId2);
        Location loc2(fileId2, line2, fC2->Column(nodeId2),
                      symbols->registerSymbol(className));

        if ((fileId1 != fileId2) || (line1 != line2)) {
          std::string diff;
          if (fC1->diffTree(nodeId1, fC2, nodeId2, &diff)) {
            locations.push_back(loc2);
          }
        }

        itr++;
        if (itr == classes.end()) {
          done = true;
          break;
        } else {
          std::string nextClassName = (*itr).first;
          ClassDefinition* nextClassDefinition = (*itr).second;
          prevClassName = nextClassName;
          prevClassDefinition = nextClassDefinition;
          if (prevClassName != className) {
            className = prevClassName;
            classDefinition = prevClassDefinition;
            break;
          }
        }
      }

      if (!locations.empty()) {
        Error err1(ErrorDefinition::COMP_MULTIPLY_DEFINED_CLASS, loc1,
                   &locations);
        errors->addError(err1);
      }
    }
    prevClassName = className;
    prevClassDefinition = classDefinition;
    if (done) break;
  }
  return true;
}

bool TestbenchElaboration::bindBaseClasses_() {
  Compiler* compiler = m_compileDesign->getCompiler();
  Design* design = compiler->getDesign();
  UHDM::Serializer& s = m_compileDesign->getSerializer();

  ClassNameClassDefinitionMultiMap classes = design->getClassDefinitions();

  // Bind base classes
  for (const auto& [className, classDefinition] : classes) {
    const FileContent* fCDef = classDefinition->getFileContent();
    for (auto& class_def : classDefinition->getMutableBaseClassMap()) {
      const DataType* placeHolder = class_def.second;
      const DataType* the_def =
          bindDataType_(class_def.first, class_def.second->getFileContent(),
                        class_def.second->getNodeId(), classDefinition,
                        ErrorDefinition::COMP_UNDEFINED_BASE_CLASS);
      const ClassDefinition* bdef =
          datatype_cast<const ClassDefinition*>(the_def);
      class_def.second = bdef;
      if (class_def.second) {
        // Super
        DataType* thisdt = new DataType(
            class_def.second->getFileContent(), class_def.second->getNodeId(),
            class_def.second->getName(), VObjectType::paClass_declaration);
        thisdt->setDefinition(class_def.second);
        Property* prop =
            new Property(thisdt, classDefinition->getFileContent(),
                         classDefinition->getNodeId(), InvalidNodeId, "super",
                         false, false, false, false, false);
        UHDM::class_defn* derived = classDefinition->getUhdmDefinition();
        UHDM::class_defn* parent = bdef->getUhdmDefinition();
        classDefinition->insertProperty(prop);
        UHDM::extends* extends = s.MakeExtends();
        extends->VpiParent(derived);
        fCDef->populateCoreMembers(placeHolder->getNodeId(),
                                   placeHolder->getNodeId(), extends);
        UHDM::class_typespec* tps = s.MakeClass_typespec();
        fCDef->populateCoreMembers(placeHolder->getNodeId(),
                                   placeHolder->getNodeId(), tps);
        extends->Class_typespec(tps);
        tps->Class_defn(parent);
        tps->VpiName(placeHolder->getName());
        derived->Extends(extends);
        UHDM::VectorOfclass_defn* all_derived = parent->Deriveds();
        if (all_derived == nullptr) {
          parent->Deriveds(s.MakeClass_defnVec());
          all_derived = parent->Deriveds();
        }
        all_derived->push_back(derived);
      } else {
        class_def.second = datatype_cast<const Parameter*>(the_def);
        if (class_def.second) {
          // Super
          DataType* thisdt = new DataType(
              class_def.second->getFileContent(), class_def.second->getNodeId(),
              class_def.second->getName(), VObjectType::paClass_declaration);
          thisdt->setDefinition(class_def.second);
          Property* prop =
              new Property(thisdt, classDefinition->getFileContent(),
                           classDefinition->getNodeId(), InvalidNodeId, "super",
                           false, false, false, false, false);
          classDefinition->insertProperty(prop);
          UHDM::extends* extends = s.MakeExtends();
          fCDef->populateCoreMembers(placeHolder->getNodeId(),
                                     placeHolder->getNodeId(), extends);
          UHDM::class_typespec* tps = s.MakeClass_typespec();
          tps->VpiName(class_def.second->getName());
          extends->Class_typespec(tps);
          UHDM::class_defn* def = classDefinition->getUhdmDefinition();
          def->Extends(extends);
        }
      }
    }
  }
  return true;
}

bool TestbenchElaboration::bindDataTypes_() {
  Compiler* compiler = m_compileDesign->getCompiler();
  Design* design = compiler->getDesign();
  ClassNameClassDefinitionMultiMap classes = design->getClassDefinitions();

  // Bind data types
  for (const auto& [className, classDefinition] : classes) {
    for (auto& datatype : classDefinition->getUsedDataTypeMap()) {
      std::string dataTypeName = datatype.first;
      DataType* dtype = datatype.second;
      if (dtype->getDefinition()) continue;
      VObjectType type = dtype->getType();
      if (type == VObjectType::slStringConst ||
          type == VObjectType::paNull_rule ||
          type == VObjectType::paClass_scope) {
        const DataType* the_def = bindDataType_(
            dataTypeName, dtype->getFileContent(), dtype->getNodeId(),
            classDefinition, ErrorDefinition::COMP_UNDEFINED_TYPE);
        if (the_def != dtype) dtype->setDefinition(the_def);
      }
    }
    for (auto& func : classDefinition->getFunctionMap()) {
      for (auto& datatype : func.second->getUsedDataTypeMap()) {
        std::string dataTypeName = datatype.first;
        DataType* dtype = datatype.second;
        if (dtype->getDefinition()) continue;
        VObjectType type = dtype->getType();
        if (type == VObjectType::slStringConst ||
            type == VObjectType::paNull_rule ||
            type == VObjectType::paClass_scope) {
          const DataType* the_def = bindDataType_(
              dataTypeName, dtype->getFileContent(), dtype->getNodeId(),
              classDefinition, ErrorDefinition::COMP_UNDEFINED_TYPE);
          if (the_def != dtype) dtype->setDefinition(the_def);
        }
      }
    }
  }
  return true;
}

bool TestbenchElaboration::bindFunctions_() {
  bindFunctionReturnTypesAndParamaters_();
  bindFunctionBodies_();
  return true;
}

bool TestbenchElaboration::bindFunctionReturnTypesAndParamaters_() {
  Compiler* compiler = m_compileDesign->getCompiler();
  ErrorContainer* errors = compiler->getErrorContainer();
  SymbolTable* symbols = compiler->getSymbolTable();
  Design* design = compiler->getDesign();
  ClassNameClassDefinitionMultiMap classes = design->getClassDefinitions();

  // Bind Function return values, parameters and body
  for (const auto& [className, classDefinition] : classes) {
    for (auto& func : classDefinition->getFunctionMap()) {
      DataType* dtype = func.second->getReturnType();
      const std::string_view dataTypeName = dtype->getName();
      if (dtype->getDefinition()) continue;
      if (dtype->getFileContent() == nullptr) continue;
      if (dtype->getType() == VObjectType::slStringConst) {
        const DataType* the_def = bindDataType_(
            dataTypeName, dtype->getFileContent(), func.second->getNodeId(),
            classDefinition, ErrorDefinition::COMP_UNDEFINED_TYPE);
        if (the_def != dtype) dtype->setDefinition(the_def);
      }
      for (auto& param : func.second->getParams()) {
        const DataType* dtype = param->getDataType();
        const std::string_view dataTypeName = dtype->getName();
        if (dtype->getDefinition()) continue;
        if (dtype->getFileContent() == nullptr) continue;
        if (dtype->getType() == VObjectType::slStringConst) {
          const DataType* the_def = bindDataType_(
              dataTypeName, dtype->getFileContent(), param->getNodeId(),
              classDefinition, ErrorDefinition::COMP_UNDEFINED_TYPE);
          if (the_def != dtype) dtype->setDefinition(the_def);
          if (the_def && the_def->isParameter()) continue;
          Value* value = param->getDefault();
          if (value) {
            if (!dtype->isCompatible(value)) {
              const std::string_view name = param->getName();
              const std::string_view typeName = dtype->getName();
              NodeId p = param->getNodeId();
              const FileContent* fC = dtype->getFileContent();
              Location loc1(
                  fC->getFileId(p), fC->Line(p), fC->Column(p),
                  symbols->registerSymbol(StrCat(name, " of type ", typeName)));
              std::string exp;
              if (value->getType() == Value::Type::String)
                exp = value->getValueS();
              else if (value->getType() == Value::Type::Double)
                exp = std::to_string(value->getValueD(0));
              else
                exp = std::to_string(value->getValueL(0));
              Location loc2(symbols->registerSymbol(exp));
              Error err1(ErrorDefinition::COMP_INCOMPATIBLE_TYPES, loc1, loc2);
              errors->addError(err1);
            }
          }
        }
      }
    }
  }
  return true;
}

bool TestbenchElaboration::bindSubRoutineCall_(ClassDefinition* classDefinition,
                                               Statement* stmt, Design* design,
                                               SymbolTable* symbols,
                                               ErrorContainer* errors) {
  std::string datatypeName;
  SubRoutineCallStmt* st = statement_cast<SubRoutineCallStmt*>(stmt);
  std::vector<std::string_view> var_chain = st->getVarChainNames();
  const std::string_view function = st->getFunc();
  bool validFunction = true;
  const DataType* dtype = nullptr;
  Variable* the_obj = nullptr;
  if (st->isStatic())
    the_obj = locateStaticVariable_(
        var_chain, st->getFileContent(), st->getNodeId(), stmt->getScope(),
        classDefinition, ErrorDefinition::ELAB_UNDEF_VARIABLE);
  else
    the_obj = locateVariable_(var_chain, st->getFileContent(), st->getNodeId(),
                              stmt->getScope(), classDefinition,
                              ErrorDefinition::ELAB_UNDEF_VARIABLE);

  if (the_obj) {
    dtype = the_obj->getDataType();
    if (dtype == nullptr) return true;
    VObjectType type = dtype->getType();
    const DataType* def = dtype->getDefinition();

    if (type == VObjectType::paClass_declaration) {
      validFunction =
          checkValidFunction(dtype, function, stmt, design, datatypeName);
    } else if (DataType::isNumber(type) || DataType::isInteger_type(type) ||
               DataType::isNon_integer_type(type) ||
               DataType::isString_type(type)) {
      if (def) {
        type = def->getType();
        dtype = def;
      }

      NodeId range = the_obj->getRange();
      if (range) {
        VObjectType rangeType = the_obj->getFileContent()->Type(range);

        if (rangeType == VObjectType::paUnsized_dimension) {
          // Vector
          validFunction = checkValidBuiltinClass_("array", function, stmt,
                                                  design, datatypeName);
        } else if (rangeType == VObjectType::paVariable_dimension) {
          const FileContent* sfC = the_obj->getFileContent();
          NodeId subRange = sfC->Child(range);
          VObjectType the_type = sfC->Type(subRange);
          if (the_type == VObjectType::paQueue_dimension) {
            // Queue

            // foreach (darray[id]) darray[id].func()
            NodeId tmp = stmt->getNodeId();
            tmp = sfC->Child(tmp);
            tmp = sfC->Sibling(tmp);
            VObjectType t = sfC->Type(tmp);
            if ((t == VObjectType::paConstant_bit_select) && sfC->Child(tmp)) {
              // there is an actual array index
              if (type == VObjectType::paClass_declaration) {
                validFunction = checkValidFunction(dtype, function, stmt,
                                                   design, datatypeName);
              }
            } else {
              validFunction = checkValidBuiltinClass_("queue", function, stmt,
                                                      design, datatypeName);
            }
          } else if (the_type == VObjectType::paUnpacked_dimension) {
            // foreach (darray[id]) darray[id].func()
            NodeId subroutine_call = stmt->getNodeId();
            NodeId var_id = sfC->Child(subroutine_call);
            NodeId constant_bit_select = sfC->Sibling(var_id);
            VObjectType t = sfC->Type(constant_bit_select);
            NodeId select_id = sfC->Child(constant_bit_select);
            if ((t == VObjectType::paConstant_bit_select) && select_id) {
              validFunction = checkValidFunction(dtype, function, stmt, design,
                                                 datatypeName);
            } else {
              validFunction = checkValidBuiltinClass_("queue", function, stmt,
                                                      design, datatypeName);
            }
          }
        }
      } else {
        validFunction =
            checkValidFunction(dtype, function, stmt, design, datatypeName);
      }
    }
  }
  if (var_chain.empty()) {
    if (st->isSystemCall()) {
      validFunction = checkValidBuiltinClass_("system", function, stmt, design,
                                              datatypeName);
      if (!validFunction) {
        const FileContent* fC = st->getFileContent();
        NodeId p = st->getNodeId();
        Location loc1(fC->getFileId(p), fC->Line(p), fC->Column(p),
                      symbols->registerSymbol(function));
        Error err1(ErrorDefinition::COMP_UNDEFINED_SYSTEM_FUNCTION, loc1);
        errors->addError(err1);
        return true;
      }
    } else {
      Function* func = classDefinition->getFunction(function);
      if (func)
        stmt->setFunction(func);
      else {
        validFunction = false;
        dtype = classDefinition;
      }

      ClassDefinition* genClass =
          design->getClassDefinition("builtin::any_sverilog_class");
      if (genClass && genClass->getFunction(function)) {
        validFunction = true;
        stmt->setFunction(genClass->getFunction(function));
      }
    }
  }

  if (validFunction == false) {
    if (dtype->isParameter()) {
      return true;
    }
    std::string name;
    for (const auto& v : var_chain) name.append(v).append(".");
    if (!name.empty()) name = name.substr(0, name.size() - 1);
    while (dtype && dtype->getDefinition()) {
      dtype = dtype->getDefinition();
    }
    if (name.empty()) {
      name = "this";
    }
    std::string_view typeName = dtype->getName();
    if (!datatypeName.empty()) typeName = datatypeName;
    NodeId p = st->getNodeId();
    const FileContent* fC = st->getFileContent();
    Location loc1(
        fC->getFileId(p), fC->Line(p), fC->Column(p),
        symbols->registerSymbol(StrCat("\"", name, "\" of type ", typeName)));
    const FileContent* fC2 = dtype->getFileContent();
    Location loc2(
        fC2->getFileId(dtype->getNodeId()), fC2->Line(dtype->getNodeId()),
        fC2->Column(dtype->getNodeId()), symbols->registerSymbol(function));
    Error err1(ErrorDefinition::COMP_NO_METHOD_FOR_TYPE, loc1, loc2);
    errors->addError(err1);
  }
  return true;
}

bool TestbenchElaboration::bindForLoop_(ClassDefinition* classDefinition,
                                        Statement* stmt, ForLoopStmt* st) {
  const FileContent* sfC = st->getFileContent();
  NodeId fid = st->getNodeId();
  VObjectType itr_type = st->getIteratorType();
  DataType* itrDataType = new DataType(sfC, fid, "integer", itr_type);
  for (const auto& itrId : st->getIteratorIds()) {
    Variable* var = new Variable(itrDataType, sfC, itrId.first, InvalidNodeId,
                                 sfC->SymName(itrId.first));
    st->getParentScope()->addVariable(var);
  }
  return true;
}

bool TestbenchElaboration::bindForeachLoop_(ClassDefinition* classDefinition,
                                            Statement* stmt,
                                            ForeachLoopStmt* st) {
  NodeId arrayId = st->getArrayId();
  const FileContent* sfC = st->getFileContent();
  std::vector<std::string_view> var_chain = computeVarChain(sfC, arrayId);
  Variable* arrayVar =
      locateVariable_(var_chain, sfC, arrayId, stmt->getScope(),
                      classDefinition, ErrorDefinition::ELAB_UNDEF_VARIABLE);
  if (arrayVar) {
    NodeId range = arrayVar->getRange();
    NodeId rangeTypeId = range;
    const DataType* itrDataType = nullptr;
    while (range) {
      rangeTypeId = range;
      range = sfC->Child(rangeTypeId);
    }
    VObjectType rangeType = sfC->Type(rangeTypeId);
    if (rangeType == VObjectType::slStringConst) {
      const std::string_view dataTypeName = sfC->SymName(rangeTypeId);
      itrDataType =
          bindDataType_(dataTypeName, sfC, rangeTypeId, classDefinition,
                        ErrorDefinition::COMP_UNDEFINED_TYPE);
    } else if (rangeType == VObjectType::paAssociative_dimension ||
               rangeType == VObjectType::paQueue_dimension) {
      // Integer Type
      itrDataType = new DataType(sfC, arrayId, "integer",
                                 VObjectType::paIntegerAtomType_Int);
    }

    for (auto itrId : st->getIteratorIds()) {
      Variable* var = new Variable(itrDataType, sfC, itrId, InvalidNodeId,
                                   sfC->SymName(itrId));
      st->getParentScope()->addVariable(var);
    }
  }
  return true;
}

bool TestbenchElaboration::bindFunctionBodies_() {
  Compiler* compiler = m_compileDesign->getCompiler();
  ErrorContainer* errors = compiler->getErrorContainer();
  SymbolTable* symbols = compiler->getSymbolTable();
  Design* design = compiler->getDesign();
  ClassNameClassDefinitionMultiMap classes = design->getClassDefinitions();

  // Bind Function return values, parameters and body
  for (const auto& [className, classDefinition] : classes) {
    for (auto& func : classDefinition->getFunctionMap()) {
      // Skip binding of parameterized classes
      if (!classDefinition->hasCompleteBaseSpecification()) continue;

      std::queue<Statement*> stmts;
      for (Statement* stmt : func.second->getStmts()) stmts.push(stmt);

      while (!stmts.empty()) {
        Statement* stmt = stmts.front();
        stmts.pop();
        for (Statement* stmt1 : stmt->getStatements()) stmts.push(stmt1);
        VObjectType stmt_type = stmt->getType();
        switch (stmt_type) {
          case VObjectType::paPs_or_hierarchical_array_identifier: {
            // Foreach loop
            ForeachLoopStmt* st = statement_cast<ForeachLoopStmt*>(stmt);
            if (st) {
              bindForeachLoop_(classDefinition, stmt, st);
            }
            break;
          }
          case VObjectType::paFor_initialization: {
            // For loop
            ForLoopStmt* st = statement_cast<ForLoopStmt*>(stmt);
            if (st) {
              bindForLoop_(classDefinition, stmt, st);
            }
            break;
          }
          case VObjectType::paSubroutine_call_statement:
            bindSubRoutineCall_(classDefinition, stmt, design, symbols, errors);
            break;
          default:
            break;
        }
      }
    }
  }
  return true;
}

bool TestbenchElaboration::bindTasks_() {
  Compiler* compiler = m_compileDesign->getCompiler();
  // ErrorContainer* errors = compiler->getErrorContainer ();
  // SymbolTable* symbols = compiler->getSymbolTable ();
  Design* design = compiler->getDesign();
  ClassNameClassDefinitionMultiMap classes = design->getClassDefinitions();

  // Bind Tasks parameters and body
  for (const auto& [className, classDefinition] : classes) {
    // Bind Tasks parameters
    for (auto& func : classDefinition->getTaskMap()) {
      for (auto param : func.second->getParams()) {
        const DataType* dtype = param->getDataType();
        const std::string_view dataTypeName = dtype->getName();
        if (dtype->getDefinition()) continue;
        if (dtype->getFileContent() == nullptr) continue;
        if (dtype->getType() == VObjectType::slStringConst) {
          const DataType* the_def = bindDataType_(
              dataTypeName, dtype->getFileContent(), param->getNodeId(),
              classDefinition, ErrorDefinition::COMP_UNDEFINED_TYPE);
          if (the_def != dtype) dtype->setDefinition(the_def);
        }
      }
    }
  }
  return true;
}

bool TestbenchElaboration::bindProperties_() {
  Compiler* compiler = m_compileDesign->getCompiler();
  Design* design = compiler->getDesign();
  UHDM::Serializer& s = m_compileDesign->getSerializer();
  ClassNameClassDefinitionMultiMap classes = design->getClassDefinitions();

  // Bind properties
  for (const auto& [className, classDefinition] : classes) {
    UHDM::class_defn* defn = classDefinition->getUhdmDefinition();
    UHDM::VectorOfvariables* vars = defn->Variables();
    UHDM::VectorOfnamed_event* events = defn->Named_events();
    for (Signal* sig : classDefinition->getSignals()) {
      const FileContent* fC = sig->getFileContent();
      NodeId id = sig->getNodeId();
      NodeId packedDimension = sig->getPackedDimension();
      NodeId unpackedDimension = sig->getUnpackedDimension();
      if (vars == nullptr) {
        vars = s.MakeVariablesVec();
        defn->Variables(vars);
      }

      const std::string_view signame = sig->getName();

      // Packed and unpacked ranges
      int32_t packedSize = 0;
      int32_t unpackedSize = 0;
      std::vector<UHDM::range*>* packedDimensions = m_helper.compileRanges(
          classDefinition, fC, packedDimension, m_compileDesign, Reduce::Yes,
          nullptr, nullptr, packedSize, false);
      std::vector<UHDM::range*>* unpackedDimensions = nullptr;
      if (fC->Type(unpackedDimension) == VObjectType::paClass_new) {
      } else {
        unpackedDimensions = m_helper.compileRanges(
            classDefinition, fC, unpackedDimension, m_compileDesign,
            Reduce::Yes, nullptr, nullptr, unpackedSize, false);
      }
      UHDM::typespec* tps = nullptr;
      NodeId typeSpecId = sig->getTypeSpecId();
      if (typeSpecId) {
        tps = m_helper.compileTypespec(classDefinition, fC, typeSpecId,
                                       m_compileDesign, Reduce::Yes, nullptr,
                                       nullptr, false);
      }
      if (tps == nullptr) {
        if (sig->getInterfaceTypeNameId()) {
          tps = m_helper.compileTypespec(
              classDefinition, fC, sig->getInterfaceTypeNameId(),
              m_compileDesign, Reduce::Yes, nullptr, nullptr, false);
        }
      }

      // Assignment to a default value
      UHDM::expr* exp =
          exprFromAssign_(classDefinition, fC, id, unpackedDimension, nullptr);
      if (exp != nullptr) exp->VpiParent(defn);

      UHDM::any* obj =
          makeVar_(classDefinition, sig, packedDimensions, packedSize,
                   unpackedDimensions, unpackedSize, nullptr, vars, exp, tps);

      if (obj) {
        if (obj->UhdmType() == UHDM::uhdmnamed_event) {
          if (events == nullptr) {
            defn->Named_events(s.MakeNamed_eventVec());
            events = defn->Named_events();
          }
          events->push_back((UHDM::named_event*)obj);
        }

        fC->populateCoreMembers(id, id, obj);
        obj->VpiParent(defn);
      } else {
        // Unsupported type
        ErrorContainer* errors =
            m_compileDesign->getCompiler()->getErrorContainer();
        SymbolTable* symbols = m_compileDesign->getCompiler()->getSymbolTable();
        Location loc(fC->getFileId(), fC->Line(id), fC->Column(id),
                     symbols->registerSymbol(signame));
        Error err(ErrorDefinition::UHDM_UNSUPPORTED_SIGNAL, loc);
        errors->addError(err);
      }
    }
  }
  return true;
}

}  // namespace SURELOG
