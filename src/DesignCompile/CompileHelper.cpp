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
 * File:   CompileHelper.cpp
 * Author: alain
 *
 * Created on May 14, 2019, 8:03 PM
 */

#include "Surelog/DesignCompile/CompileHelper.h"

#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Common/NodeId.h"
#include "Surelog/Common/PathId.h"
#include "Surelog/Common/Session.h"
#include "Surelog/Design/DataType.h"
#include "Surelog/Design/DummyType.h"
#include "Surelog/Design/Enum.h"
#include "Surelog/Design/FileCNodeId.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/Design/ModuleDefinition.h"
#include "Surelog/Design/ModuleInstance.h"
#include "Surelog/Design/Netlist.h"
#include "Surelog/Design/ParamAssign.h"
#include "Surelog/Design/Parameter.h"
#include "Surelog/Design/Signal.h"
#include "Surelog/Design/SimpleType.h"
#include "Surelog/Design/Struct.h"
#include "Surelog/Design/TfPortItem.h"
#include "Surelog/Design/Union.h"
#include "Surelog/Design/VObject.h"
#include "Surelog/Design/ValuedComponentI.h"
#include "Surelog/DesignCompile/CompileDesign.h"
#include "Surelog/DesignCompile/UhdmWriter.h"
#include "Surelog/ErrorReporting/Error.h"
#include "Surelog/ErrorReporting/ErrorContainer.h"
#include "Surelog/ErrorReporting/ErrorDefinition.h"
#include "Surelog/ErrorReporting/Location.h"
#include "Surelog/Library/Library.h"
#include "Surelog/Package/Package.h"
#include "Surelog/SourceCompile/Compiler.h"
#include "Surelog/SourceCompile/SymbolTable.h"
#include "Surelog/SourceCompile/VObjectTypes.h"
#include "Surelog/Testbench/ClassDefinition.h"
#include "Surelog/Testbench/Program.h"
#include "Surelog/Testbench/TypeDef.h"
#include "Surelog/Testbench/Variable.h"
#include "Surelog/Utils/NumUtils.h"
#include "Surelog/Utils/StringUtils.h"

// UHDM
#include <uhdm/BaseClass.h>
#include <uhdm/ElaboratorListener.h>
#include <uhdm/ExprEval.h>
#include <uhdm/VpiListener.h>
#include <uhdm/clone_tree.h>
#include <uhdm/expr.h>
#include <uhdm/sv_vpi_user.h>
#include <uhdm/uhdm.h>
#include <uhdm/uhdm_types.h>
#include <uhdm/vpi_user.h>

#include <algorithm>
#include <climits>
#include <cstdint>
#include <cstring>
#include <functional>
#include <iostream>
#include <map>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace SURELOG {

CompileHelper::CompileHelper(Session* session)
    : m_session(session), m_exprBuilder(session) {}

void CompileHelper::checkForLoops(bool on) {
  m_checkForLoops = on;
  m_stackLevel = 0;
  m_unwind = false;
}

bool CompileHelper::loopDetected(PathId fileId, uint32_t lineNumber,
                                 CompileDesign* compileDesign,
                                 ValuedComponentI* instance) {
#if defined(_WIN32) || defined(__MINGW32__) || defined(__CYGWIN__)
  constexpr int32_t kMaxAllowedStackDepth = 100;
#else
  constexpr int32_t kMaxAllowedStackDepth = 1000;
#endif
  if (m_checkForLoops) {
    if ((m_stackLevel > kMaxAllowedStackDepth) || (m_unwind)) {
      std::string instName;
      if (ModuleInstance* inst =
              valuedcomponenti_cast<ModuleInstance*>(instance)) {
        instName = inst->getFullPathName();
      }
      Location loc(fileId, lineNumber, 0,
                   m_session->getSymbolTable()->registerSymbol(instName));
      m_session->getErrorContainer()->addError(
          ErrorDefinition::ELAB_EXPRESSION_LOOP, loc);
      m_unwind = true;
      return true;
    }
  }
  return false;
}

bool CompileHelper::importPackage(DesignComponent* scope, Design* design,
                                  const FileContent* fC, NodeId id,
                                  CompileDesign* compileDesign,
                                  bool inPackage) {
  NodeId nameId = fC->Child(id);
  const std::string_view pack_name = fC->SymName(nameId);
  Package* def = design->getPackage(pack_name);

  if (def == nullptr) {
    Location loc(fC->getFileId(id), fC->Line(id), fC->Column(id),
                 m_session->getSymbolTable()->registerSymbol(pack_name));
    m_session->getErrorContainer()->addError(
        ErrorDefinition::COMP_UNDEFINED_PACKAGE, loc);
    return true;
  }

  if (def == scope) return true;  // Skip

  scope->addAccessPackage(def);
  if (m_elaborate == Elaborate::No) return true;

  uhdm::Serializer& s = compileDesign->getSerializer();
  FileCNodeId fnid(fC, id);
  scope->addObject(VObjectType::paPackage_import_item, fnid);

  std::string object_name;
  if (NodeId objId = fC->Sibling(nameId)) {
    if (fC->Type(objId) == VObjectType::slStringConst) {
      object_name = fC->SymName(objId);
    }
  }

  auto& classSet = def->getObjects(VObjectType::paClass_declaration);
  for (const auto& cls : classSet) {
    const FileContent* packageFile = cls.fC;
    NodeId classDef = packageFile->Sibling(cls.nodeId);
    const std::string_view name = packageFile->SymName(classDef);
    if (!object_name.empty() && (name != object_name)) continue;
    std::string fullName = StrCat(def->getName(), "::", name);
    DesignComponent* comp = packageFile->getComponentDefinition(fullName);
    FileCNodeId fnid(packageFile, classDef);
    scope->addNamedObject(name, fnid, comp);
    scope->insertDataType(name, (ClassDefinition*)comp);
  }
  // Typespecs
  auto& typeSet = def->getDataTypeMap();
  for (auto& type : typeSet) {
    if (!object_name.empty()) {
      if (type.first != object_name) continue;
    }
    scope->insertDataType(type.first, type.second);
  }
  // Variables
  auto& variableSet = def->getVariables();
  for (auto& var : variableSet) {
    if (!object_name.empty()) {
      if (var.first != object_name) continue;
    }
    scope->addVariable(var.second);
    if (Value* val = def->getValue(var.first)) {
      scope->setValue(var.first, m_exprBuilder.clone(val), m_exprBuilder);
    }
  }
  // Nets
  auto& netSet = def->getSignals();
  for (auto& net : netSet) {
    if (!object_name.empty()) {
      if (net->getName() != object_name) continue;
    }
    scope->addSignal(net);
  }

  // Type parameters
  auto& paramSet = def->getParameterMap();
  for (auto& param : paramSet) {
    if (!object_name.empty()) {
      if (param.first != object_name) continue;
    }
    Parameter* orig = param.second;
    Parameter* clone = new Parameter(*orig);
    clone->setImportedPackage(pack_name);
    scope->insertParameter(clone);
    uhdm::Any* p = orig->getUhdmParam();

    uhdm::AnyCollection* parameters = scope->getParameters();
    if (parameters == nullptr) {
      scope->setParameters(s.makeCollection<uhdm::Any>());
      parameters = scope->getParameters();
    }

    if (p) {
      uhdm::ElaboratorContext elaboratorContext(&s, false, true);
      uhdm::Any* pclone = uhdm::clone_tree(p, &elaboratorContext);
      if (pclone->getUhdmType() == uhdm::UhdmType::TypeParameter) {
        uhdm::TypeParameter* the_p = (uhdm::TypeParameter*)pclone;
        the_p->setImported(pack_name);
      } else {
        uhdm::Parameter* the_p = (uhdm::Parameter*)pclone;
        the_p->setImported(pack_name);
      }
      parameters->emplace_back(pclone);
      clone->setUhdmParam(pclone);
    }
  }

  // Regular parameter
  auto& params = def->getParamAssignVec();
  for (ParamAssign* orig : params) {
    if (!object_name.empty()) {
      uhdm::ParamAssign* pass = orig->getUhdmParamAssign();
      if (pass->getLhs()->getName() != object_name) continue;
    }
    ParamAssign* clone = new ParamAssign(*orig);
    scope->addParamAssign(clone);
    uhdm::ParamAssign* pass = clone->getUhdmParamAssign();

    uhdm::ParamAssignCollection* param_assigns = scope->getParamAssigns();
    if (param_assigns == nullptr) {
      scope->setParam_assigns(s.makeCollection<uhdm::ParamAssign>());
      param_assigns = scope->getParamAssigns();
    }
    uhdm::AnyCollection* parameters = scope->getParameters();
    if (parameters == nullptr) {
      scope->setParameters(s.makeCollection<uhdm::Any>());
      parameters = scope->getParameters();  // NOLINT(*.DeadStores)
    }

    uhdm::ElaboratorContext elaboratorContext(&s, false, true);
    uhdm::ParamAssign* cpass =
        (uhdm::ParamAssign*)uhdm::clone_tree(pass, &elaboratorContext);
    clone->setUhdmParamAssign(cpass);
    param_assigns->emplace_back(cpass);
    uhdm::Any* orig_p = (uhdm::Any*)cpass->getLhs();
    uhdm::Any* pclone =
        orig_p;  // The param_assign clone already cloned the param
    cpass->setLhs(pclone);
    if (pclone->getUhdmType() == uhdm::UhdmType::Parameter) {
      uhdm::Parameter* the_p = (uhdm::Parameter*)pclone;
      the_p->setImported(pack_name);
    }
  }

  // Values (from enum declarations...)
  auto& values = def->getMappedValues();
  for (auto& mvalue : values) {
    if (!object_name.empty()) {
      if (mvalue.first != object_name) continue;
    }
    if (mvalue.second.first->isValid())
      scope->setValue(mvalue.first, m_exprBuilder.clone(mvalue.second.first),
                      m_exprBuilder, mvalue.second.second);
  }
  for (auto& cvalue : def->getComplexValues()) {
    if (!object_name.empty()) {
      if (cvalue.first != object_name) continue;
    }
    scope->setComplexValue(cvalue.first, cvalue.second);
  }

  // tasks/functions
  uhdm::TaskFuncCollection* funcs = def->getTaskFuncs();
  if (funcs) {
    uhdm::TaskFuncCollection* sfuncs = scope->getTaskFuncs();
    if (sfuncs == nullptr) {
      sfuncs = s.makeCollection<uhdm::TaskFunc>();
      scope->setTaskFuncs(sfuncs);
    }
    for (auto& func : *funcs) {
      if (!object_name.empty()) {
        if (func->getName() != object_name) continue;
      }
      bool duplicate = false;
      for (auto& f : *sfuncs) {
        if (f->getName() == func->getName()) {
          duplicate = true;
          break;
        }
      }
      if (!duplicate) {
        if (inPackage) {
          uhdm::ElaboratorContext elaboratorContext(&s, false,
                                                    /*mute errors */ true);
          uhdm::TaskFunc* clone = (uhdm::TaskFunc*)uhdm::clone_tree(
              (uhdm::Any*)func, &elaboratorContext);
          sfuncs->emplace_back(clone);
        } else {
          sfuncs->emplace_back(func);
        }
      }
    }
  }

  return true;
}

uhdm::Constant* CompileHelper::constantFromValue(Value* val,
                                                 CompileDesign* compileDesign) {
  uhdm::Serializer& s = compileDesign->getSerializer();
  Value::Type valueType = val->getType();
  uhdm::Constant* c = nullptr;
  switch (valueType) {
    case Value::Type::Scalar: {
      c = s.make<uhdm::Constant>();
      c->setConstType(vpiScalarVal);
      c->setValue(val->uhdmValue());
      c->setDecompile(val->decompiledValue());
      c->setSize(1);
      break;
    }
    case Value::Type::Binary: {
      c = s.make<uhdm::Constant>();
      c->setConstType(vpiBinStrVal);
      c->setValue(val->uhdmValue());
      c->setDecompile(val->decompiledValue());
      c->setSize(val->getSize());
      break;
    }
    case Value::Type::Hexadecimal: {
      c = s.make<uhdm::Constant>();
      c->setConstType(vpiHexStrVal);
      c->setValue(val->uhdmValue());
      c->setDecompile(val->decompiledValue());
      c->setSize(val->getSize());
      break;
    }
    case Value::Type::Octal: {
      c = s.make<uhdm::Constant>();
      c->setConstType(vpiOctStrVal);
      c->setValue(val->uhdmValue());
      c->setDecompile(val->decompiledValue());
      c->setSize(val->getSize());
      break;
    }
    case Value::Type::Unsigned:
    case Value::Type::Integer: {
      c = s.make<uhdm::Constant>();
      c->setConstType(vpiIntVal);
      c->setValue(val->uhdmValue());
      c->setDecompile(val->decompiledValue());
      c->setSize(val->getSize());
      break;
    }
    case Value::Type::Double: {
      c = s.make<uhdm::Constant>();
      c->setConstType(vpiRealVal);
      c->setValue(val->uhdmValue());
      c->setDecompile(val->decompiledValue());
      c->setSize(val->getSize());
      break;
    }
    case Value::Type::String: {
      c = s.make<uhdm::Constant>();
      c->setConstType(vpiStringVal);
      c->setValue(val->uhdmValue());
      c->setDecompile(val->decompiledValue());
      c->setSize(val->getSize());
      break;
    }
    case Value::Type::None:
    default: {
      // return nullptr
    }
  }
  return c;
}

bool CompileHelper::compileTfPortList(Procedure* parent, const FileContent* fC,
                                      NodeId tf_port_list,
                                      TfPortList& targetList) {
  bool result = true;
  /*
   n<c1> u<7> t<StringConst> p<29> s<27> l<10>
   n<> u<8> t<IntegerAtomType_Int> p<9> l<12>
   n<> u<9> t<Data_type> p<10> c<8> l<12>
   n<> u<10> t<Function_data_type> p<11> c<9> l<12>
   n<> u<11> t<Function_data_type_or_implicit> p<24> c<10> s<12> l<12>
   n<try_get> u<12> t<StringConst> p<24> s<22> l<12>
   n<> u<13> t<IntegerAtomType_Int> p<14> l<12>
   n<> u<14> t<Data_type> p<15> c<13> l<12>
   n<> u<15> t<Data_type_or_implicit> p<21> c<14> s<16> l<12>
   n<keyCount> u<16> t<StringConst> p<21> s<20> l<12>
   n<1> u<17> t<IntConst> p<18> l<12>
   n<> u<18> t<Primary_literal> p<19> c<17> l<12>
   n<> u<19> t<Primary> p<20> c<18> l<12>
   n<> u<20> t<Expression> p<21> c<19> l<12>
   n<> u<21> t<Tf_port_item> p<22> c<15> l<12>
   n<> u<22> t<Tf_port_list> p<24> c<21> s<23> l<12>
   n<> u<23> t<Endfunction> p<24> l<13>
   n<> u<24> t<Function_body_declaration> p<25> c<11> l<12>
   n<> u<25> t<Function_declaration> p<26> c<24> l<12>
   n<> u<26> t<Class_method> p<27> c<25> l<12>
  */
  /*
   Or
   n<get> u<47> t<StringConst> p<55> s<53> l<18>
   n<> u<48> t<PortDir_Ref> p<49> l<18>
   n<> u<49> t<Tf_port_direction> p<52> c<48> s<50> l<18>
   n<> u<50> t<Data_type_or_implicit> p<52> s<51> l<18>
   n<message> u<51> t<StringConst> p<52> l<18>
   n<> u<52> t<Tf_port_item> p<53> c<49> l<18>
  */
  // Compile arguments
  if (tf_port_list && (fC->Type(tf_port_list) == VObjectType::paTf_port_list)) {
    NodeId tf_port_item = fC->Child(tf_port_list);
    while (tf_port_item) {
      Value* value = nullptr;
      NodeId tf_data_type_or_implicit = fC->Child(tf_port_item);
      NodeId tf_data_type = fC->Child(tf_data_type_or_implicit);
      VObjectType tf_port_direction_type = fC->Type(tf_data_type_or_implicit);
      NodeId tf_param_name = fC->Sibling(tf_data_type_or_implicit);
      if (tf_port_direction_type == VObjectType::paTfPortDir_Ref ||
          tf_port_direction_type == VObjectType::paTfPortDir_ConstRef ||
          tf_port_direction_type == VObjectType::paTfPortDir_Inp ||
          tf_port_direction_type == VObjectType::paTfPortDir_Out ||
          tf_port_direction_type == VObjectType::paTfPortDir_Inout) {
        tf_data_type = fC->Sibling(tf_data_type_or_implicit);
        tf_param_name = fC->Sibling(tf_data_type);
      } else {
        tf_port_direction_type = VObjectType::sl_INVALID_;
      }
      NodeId type = fC->Child(tf_data_type);
      VObjectType the_type = fC->Type(type);
      std::string typeName;
      if (the_type == VObjectType::slStringConst) {
        typeName = fC->SymName(type);
      } else if (the_type == VObjectType::paClass_scope) {
        NodeId class_type = fC->Child(type);
        NodeId class_name = fC->Child(class_type);
        NodeId symb_id = fC->Sibling(type);
        typeName.assign(fC->SymName(class_name))
            .append("::")
            .append(fC->SymName(symb_id));
      } else {
        typeName = VObject::getTypeName(the_type);
      }
      const std::string_view name = fC->SymName(tf_param_name);
      NodeId expression = fC->Sibling(tf_param_name);
      DataType* dtype = new DataType(fC, type, typeName, fC->Type(type));

      if (expression &&
          (fC->Type(expression) != VObjectType::paVariable_dimension) &&
          (dtype->getType() != VObjectType::slStringConst)) {
        value = m_exprBuilder.evalExpr(fC, expression, parent->getParent());
      }
      NodeId range;
      TfPortItem* param = new TfPortItem(parent, fC, tf_port_item, range, name,
                                         dtype, value, tf_port_direction_type);
      targetList.emplace_back(param);
      tf_port_item = fC->Sibling(tf_port_item);
    }
  }
  return result;
}

const DataType* CompileHelper::compileTypeDef(DesignComponent* scope,
                                              const FileContent* fC,
                                              NodeId data_declaration,
                                              CompileDesign* compileDesign,
                                              Reduce reduce, uhdm::Any* pstmt) {
  DataType* newType = nullptr;
  uhdm::Serializer& s = compileDesign->getSerializer();
  if (pstmt == nullptr) pstmt = scope->getUhdmModel();
  if (pstmt == nullptr)
    pstmt = compileDesign->getCompiler()->getDesign()->getUhdmDesign();

  /*
   n<> u<1> t<IntVec_TypeBit> p<12> s<11> l<5>
   n<1> u<2> t<IntConst> p<3> l<5>
   n<> u<3> t<Primary_literal> p<4> c<2> l<5>
   n<> u<4> t<Constant_primary> p<5> c<3> l<5>
   n<> u<5> t<Constant_expression> p<10> c<4> s<9> l<5>
   n<0> u<6> t<IntConst> p<7> l<5>
   n<> u<7> t<Primary_literal> p<8> c<6> l<5>
   n<> u<8> t<Constant_primary> p<9> c<7> l<5>
   n<> u<9> t<Constant_expression> p<10> c<8> l<5>
   n<> u<10> t<Constant_range> p<11> c<5> l<5>
   n<> u<11> t<Packed_dimension> p<12> c<10> l<5>
   n<> u<12> t<Enum_base_type> p<21> c<1> s<14> l<5>
   n<UVM_INFO> u<13> t<StringConst> p<14> l<7>
   n<> u<14> t<Enum_name_declaration> p<21> c<13> s<16> l<7>
   n<UVM_WARNING> u<15> t<StringConst> p<16> l<8>
   n<> u<16> t<Enum_name_declaration> p<21> c<15> s<18> l<8>
   n<UVM_ERROR> u<17> t<StringConst> p<18> l<9>
   n<> u<18> t<Enum_name_declaration> p<21> c<17> s<20> l<9>
   n<UVM_FATAL> u<19> t<StringConst> p<20> l<10>
   n<> u<20> t<Enum_name_declaration> p<21> c<19> l<10>
   n<> u<21> t<Data_type> p<23> c<12> s<22> l<5>
   n<uvm_severity> u<22> t<StringConst> p<23> l<11>
   n<> u<23> t<Type_declaration> p<24> c<21> l<5>
   n<> u<24> t<Data_declaration> p<25> c<23> l<5>
   */

  NodeId type_declaration = fC->Child(data_declaration);
  NodeId data_type = fC->Child(type_declaration);

  VObjectType dtype = fC->Type(data_type);
  NodeId type_name;
  if (dtype == VObjectType::paClass_keyword ||
      dtype == VObjectType::paStruct_keyword ||
      dtype == VObjectType::paUnion_keyword ||
      dtype == VObjectType::paInterface_class_keyword ||
      dtype == VObjectType::paEnum_keyword) {
    type_name = fC->Sibling(data_type);
    const std::string_view name = fC->SymName(type_name);
    const TypeDef* prevDef = scope->getTypeDef(name);
    if (prevDef) return prevDef;
    if (fC->Type(type_name) == VObjectType::slStringConst) {
      TypeDef* newTypeDef = new TypeDef(fC, type_declaration, type_name, name);
      scope->insertTypeDef(newTypeDef);
      newType = newTypeDef;
      return newType;
    }
  } else if (dtype == VObjectType::slStringConst) {
    NodeId btype = data_type;
    NodeId Select = fC->Sibling(btype);
    if (fC->Type(Select) == VObjectType::paConstant_bit_select) {
      NodeId subType = fC->Sibling(Select);
      NodeId nameId = fC->Sibling(subType);
      if (nameId) {
        data_type = subType;
      } else {
        return nullptr;
      }
      type_name = fC->Sibling(data_type);
      data_type = btype;
    }
  } else {
    if (dtype != VObjectType::paData_type) {
      return nullptr;
    }
    type_name = fC->Sibling(data_type);
  }

  const NodeId Variable_dimension = fC->Sibling(type_name);
  uhdm::ArrayTypespec* array_tps = nullptr;
  uhdm::PackedArrayTypespec* packed_array_tps = nullptr;
  uhdm::Function* resolution_func = nullptr;
  std::string resolutionFunctionName;
  if (Variable_dimension) {
    if (fC->Type(Variable_dimension) == VObjectType::slStringConst) {
      std::string_view name = fC->SymName(Variable_dimension);
      std::pair<uhdm::TaskFunc*, DesignComponent*> ret =
          getTaskFunc(name, scope, compileDesign, nullptr, nullptr);
      uhdm::TaskFunc* tf = ret.first;
      resolution_func = any_cast<uhdm::Function*>(tf);
      resolutionFunctionName = name;
    } else {
      array_tps = s.make<uhdm::ArrayTypespec>();
      array_tps->setParent(pstmt);
      fC->populateCoreMembers(type_name, Variable_dimension, array_tps);
      int32_t size;
      if (uhdm::RangeCollection* ranges =
              compileRanges(scope, fC, Variable_dimension, compileDesign,
                            reduce, array_tps, nullptr, size, false)) {
        array_tps->setRanges(ranges);
      }
    }
  }
  std::string_view name = fC->SymName(type_name);
  std::string fullName(name);
  if (Package* pack = valuedcomponenti_cast<Package>(scope)) {
    fullName.assign(pack->getName()).append("::").append(name);
  }
  if (scope) {
    const TypeDef* prevDef = scope->getTypeDef(name);
    if (prevDef && !prevDef->isForwardDeclaration()) {
      SymbolTable* const symbols = m_session->getSymbolTable();
      ErrorContainer* const errors = m_session->getErrorContainer();
      Location loc1(fC->getFileId(data_type), fC->Line(data_type),
                    fC->Column(data_type), symbols->registerSymbol(name));
      const FileContent* prevFile = prevDef->getFileContent();
      NodeId prevNode = prevDef->getNodeId();
      Location loc2(prevFile->getFileId(prevNode), prevFile->Line(prevNode),
                    prevFile->Column(prevNode), symbols->registerSymbol(name));
      errors->addError(ErrorDefinition::COMP_MULTIPLY_DEFINED_TYPEDEF, loc1,
                       loc2);
    }
  }

  VObjectType base_type = fC->Type(data_type);

  DataType* type = new DataType(fC, data_type, name, base_type);
  if (scope) scope->insertDataType(name, type);

  // Enum or Struct or Union
  NodeId enum_base_type = fC->Child(data_type);
  bool enumType = false;
  bool structType = false;
  NodeId Packed_dimension = fC->Sibling(enum_base_type);
  if (Packed_dimension &&
      (fC->Type(Packed_dimension) == VObjectType::paPacked_dimension)) {
    packed_array_tps = s.make<uhdm::PackedArrayTypespec>();
    packed_array_tps->setParent(pstmt);
    fC->populateCoreMembers(data_type, data_type, packed_array_tps);
    int32_t size;
    if (uhdm::RangeCollection* ranges =
            compileRanges(scope, fC, Packed_dimension, compileDesign, reduce,
                          packed_array_tps, nullptr, size, false)) {
      packed_array_tps->setRanges(ranges);
    }
  }
  NodeId enum_name_declaration;
  if (fC->Type(enum_base_type) == VObjectType::paEnum_base_type) {
    enum_name_declaration = fC->Sibling(enum_base_type);
    enumType = true;
  } else if (fC->Type(enum_base_type) == VObjectType::paEnum_name_declaration) {
    enumType = true;
    enum_name_declaration = enum_base_type;
    enum_base_type = InvalidNodeId;
  } else if (fC->Type(enum_base_type) == VObjectType::paStruct_union) {
    structType = true;
    NodeId struct_or_union = fC->Child(enum_base_type);
    VObjectType struct_or_union_type = fC->Type(struct_or_union);
    TypeDef* newTypeDef = new TypeDef(fC, type_declaration, type_name, name);

    if (struct_or_union_type == VObjectType::paStruct_keyword) {
      Struct* st = new Struct(fC, type_name, enum_base_type);
      newTypeDef->setDataType(st);
      newTypeDef->setDefinition(st);
      uhdm::Typespec* ts = compileTypespec(scope, fC, data_type, compileDesign,
                                           reduce, pstmt, nullptr, false);
      if ((m_reduce == Reduce::Yes) && (reduce == Reduce::Yes) &&
          (valuedcomponenti_cast<Package>(scope))) {
        ts->setInstance(scope->getUhdmModel<uhdm::Instance>());
      }
      if (array_tps) {
        st->setTypespec(array_tps);
        if (array_tps->getElemTypespec() == nullptr) {
          uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
          rt->setParent(array_tps);
          array_tps->setElemTypespec(rt);
        }
        array_tps->getElemTypespec()->setActual(ts);
        array_tps->setName(fullName);
      } else if (packed_array_tps) {
        st->setTypespec(packed_array_tps);
        if (packed_array_tps->getElemTypespec() == nullptr) {
          uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
          rt->setParent(packed_array_tps);
          packed_array_tps->setElemTypespec(rt);
        }
        packed_array_tps->getElemTypespec()->setActual(ts);
        packed_array_tps->setName(fullName);
      } else {
        ts->setName(fullName);
        st->setTypespec(ts);
      }
    } else if (struct_or_union_type == VObjectType::paUnion_keyword) {
      Union* st = new Union(fC, type_name, enum_base_type);
      newTypeDef->setDataType(st);
      newTypeDef->setDefinition(st);
      uhdm::Typespec* ts =
          compileTypespec(scope, fC, enum_base_type, compileDesign, reduce,
                          pstmt, nullptr, false);
      fC->populateCoreMembers(enum_base_type, type_name, ts, true);
      if ((m_reduce == Reduce::Yes) && (reduce == Reduce::Yes) &&
          (valuedcomponenti_cast<Package>(scope))) {
        ts->setInstance(scope->getUhdmModel<uhdm::Instance>());
      }
      if (array_tps) {
        st->setTypespec(array_tps);
        if (array_tps->getElemTypespec() == nullptr) {
          uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
          rt->setParent(array_tps);
          array_tps->setElemTypespec(rt);
        }
        array_tps->getElemTypespec()->setActual(ts);
        array_tps->setName(fullName);
      } else if (packed_array_tps) {
        st->setTypespec(packed_array_tps);
        if (packed_array_tps->getElemTypespec() == nullptr) {
          uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
          rt->setParent(packed_array_tps);
          packed_array_tps->setElemTypespec(rt);
        }
        packed_array_tps->getElemTypespec()->setActual(ts);
        packed_array_tps->setName(fullName);
      } else {
        ts->setName(fullName);
        st->setTypespec(ts);
      }
    }

    if (scope) {
      DesignComponent::DataTypeMap dmap = scope->getDataTypeMap();
      DesignComponent::DataTypeMap::iterator itr = dmap.find(name);
      if (itr != dmap.end()) {
        dmap.erase(itr);
      }
    }

    type->setDefinition(newTypeDef);
    if (scope) scope->insertTypeDef(newTypeDef);
    newType = newTypeDef;
  }
  if (enumType) {
    TypeDef* newTypeDef =
        new TypeDef(fC, type_declaration, enum_base_type, name);
    int32_t val = 0;
    Enum* the_enum = new Enum(fC, type_name, enum_base_type);
    newTypeDef->setDataType(the_enum);
    newTypeDef->setDefinition(the_enum);
    the_enum->setBaseTypespec(
        compileTypespec(scope, fC, fC->Child(enum_base_type), compileDesign,
                        reduce, pstmt, nullptr, false));

    uhdm::EnumTypespec* enum_t = s.make<uhdm::EnumTypespec>();
    enum_t->setParent(pstmt);

    if (array_tps) {
      the_enum->setTypespec(array_tps);
      if (array_tps->getElemTypespec() == nullptr) {
        uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
        rt->setParent(array_tps);
        array_tps->setElemTypespec(rt);
      }
      array_tps->getElemTypespec()->setActual(enum_t);
      array_tps->setName(name);
    } else if (packed_array_tps) {
      the_enum->setTypespec(packed_array_tps);
      if (packed_array_tps->getElemTypespec() == nullptr) {
        uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
        rt->setParent(packed_array_tps);
        packed_array_tps->setElemTypespec(rt);
      }
      packed_array_tps->getElemTypespec()->setActual(enum_t);
      packed_array_tps->setName(name);
    } else {
      enum_t->setName(fullName);
      the_enum->setTypespec(enum_t);
    }

    the_enum->getFileContent()->populateCoreMembers(data_type, type_name,
                                                    enum_t);

    // Enum basetype
    if (uhdm::Typespec* basets = the_enum->getBaseTypespec()) {
      if (enum_t->getBaseTypespec() == nullptr) {
        uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
        rt->setParent(enum_t);
        the_enum->getFileContent()->populateCoreMembers(enum_base_type,
                                                        enum_base_type, rt);
        enum_t->setBaseTypespec(rt);
      }
      enum_t->getBaseTypespec()->setActual(basets);
    }
    if ((m_reduce == Reduce::Yes) && (reduce == Reduce::Yes) &&
        (valuedcomponenti_cast<Package>(scope))) {
      enum_t->setInstance(scope->getUhdmModel<uhdm::Instance>());
    }
    // Enum values
    uhdm::EnumConstCollection* econsts = enum_t->getEnumConsts(true);
    uint64_t baseSize = 64;
    if (const uhdm::RefTypespec* rt = enum_t->getBaseTypespec()) {
      if (const uhdm::Typespec* ts = rt->getActual()) {
        bool invalidValue = false;
        baseSize = Bits(ts, invalidValue, scope, compileDesign, reduce, nullptr,
                        fC->getFileId(), ts->getStartLine(), true);
      }
    }
    while (enum_name_declaration) {
      NodeId enumNameId = fC->Child(enum_name_declaration);
      const std::string_view enumName = fC->SymName(enumNameId);
      NodeId enumValueId = fC->Sibling(enumNameId);
      Value* value = nullptr;
      if (enumValueId) {
        uhdm::Any* exp = compileExpression(
            scope, fC, enumValueId, compileDesign, reduce, pstmt, nullptr);
        if (exp && (exp->getUhdmType() == uhdm::UhdmType::Constant)) {
          uhdm::Constant* c = (uhdm::Constant*)exp;
          value = m_exprBuilder.fromVpiValue(c->getValue(), c->getSize());
        } else {
          value = m_exprBuilder.evalExpr(fC, enumValueId, scope);
          value->setValid();
        }
      }
      if (value == nullptr) {
        value = m_exprBuilder.getValueFactory().newLValue();
        value->set(val, Value::Type::Integer, baseSize);
      }
      the_enum->addValue(enumName, fC->Line(enumNameId), value);
      val++;
      if (scope) scope->setValue(enumName, value, m_exprBuilder);
      Variable* variable =
          new Variable(type, fC, enumValueId, InvalidNodeId, enumName);
      if (scope) scope->addVariable(variable);

      uhdm::EnumConst* econst = s.make<uhdm::EnumConst>();
      econst->setName(enumName);
      econst->setParent(enum_t);
      fC->populateCoreMembers(enum_name_declaration, enum_name_declaration,
                              econst);
      econst->setValue(value->uhdmValue());
      if (enumValueId) {
        if (uhdm::Any* exp =
                compileExpression(scope, fC, enumValueId, compileDesign, reduce,
                                  econst, nullptr)) {
          uhdm::ExprEval eval;
          econst->setDecompile(eval.prettyPrint(exp));
        }
      } else {
        econst->setDecompile(value->decompiledValue());
      }
      econst->setSize(value->getSize());
      econsts->emplace_back(econst);
      enum_name_declaration = fC->Sibling(enum_name_declaration);
    }

    type->setDefinition(newTypeDef);
    if (scope) scope->insertTypeDef(newTypeDef);
    newType = newTypeDef;

  } else if (structType) {
  } else {
    bool forwardDeclaration = false;
    NodeId stype = fC->Child(data_type);
    if (fC->Type(stype) == VObjectType::paVIRTUAL) stype = fC->Sibling(stype);
    if (!stype && (fC->Type(data_type) == VObjectType::slStringConst)) {
      stype = data_type;
      if (!fC->Sibling(stype)) {
        name = fC->SymName(stype);
        forwardDeclaration = true;
      }
    }
    if ((fC->Type(stype) == VObjectType::slStringConst) ||
        fC->Type(stype) == VObjectType::paClass_scope) {
      TypeDef* newTypeDef =
          new TypeDef(fC, type_declaration, stype, name, forwardDeclaration);
      type->setDefinition(newTypeDef);
      if (scope) scope->insertTypeDef(newTypeDef);
      DummyType* dummy = new DummyType(fC, type_name, stype);
      newTypeDef->setDataType(dummy);
      newTypeDef->setDefinition(dummy);
      // Don't create the typespec here, as it is most likely going to be
      // incomplete at compilation time, except for packages and FileContent
      if ((m_reduce == Reduce::Yes) && (reduce == Reduce::Yes) &&
          (valuedcomponenti_cast<Package>(scope) ||
           valuedcomponenti_cast<FileContent*>(scope))) {
        uhdm::Typespec* ts = compileTypespec(scope, fC, stype, compileDesign,
                                             reduce, pstmt, nullptr, false);
        if (ts && (ts->getUhdmType() != uhdm::UhdmType::ClassTypespec) &&
            (ts->getUhdmType() != uhdm::UhdmType::UnsupportedTypespec)) {
          uhdm::ElaboratorContext elaboratorContext(&s, false, true);
          uhdm::Typespec* tpclone = (uhdm::Typespec*)uhdm::clone_tree(
              (uhdm::Any*)ts, &elaboratorContext);
          uhdm::TypedefTypespec* tpclone_typedef =
              any_cast<uhdm::TypedefTypespec>(tpclone);
          if ((tpclone_typedef != nullptr) &&
              (tpclone_typedef->getTypedefAlias() == nullptr)) {
            uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
            tsRef->setParent(tpclone);
            tpclone_typedef->setTypedefAlias(tsRef);
          }

          if (array_tps) {
            array_tps->setInstance(scope->getUhdmModel<uhdm::Instance>());
            array_tps->setName(name);
            if (array_tps->getElemTypespec() == nullptr) {
              uhdm::RefTypespec* tpcloneRef = s.make<uhdm::RefTypespec>();
              tpcloneRef->setParent(array_tps);
              array_tps->setElemTypespec(tpcloneRef);
            }
            array_tps->getElemTypespec()->setActual(tpclone);

            if (tpclone_typedef != nullptr) {
              tpclone_typedef->getTypedefAlias()->setActual(ts);
            }
            newTypeDef->setTypespec(array_tps);
            dummy->setTypespec(array_tps);
            if (resolution_func) {
              array_tps->setResolutionFunc(resolution_func);
            }
          } else if (packed_array_tps) {
            if (tpclone->getUhdmType() == uhdm::UhdmType::LogicTypespec) {
              uhdm::LogicTypespec* logic_array_tps =
                  s.make<uhdm::LogicTypespec>();
              logic_array_tps->setRanges(packed_array_tps->getRanges());
              logic_array_tps->setInstance(
                  scope->getUhdmModel<uhdm::Instance>());
              logic_array_tps->setName(name);
              if (logic_array_tps->getElemTypespec() == nullptr) {
                uhdm::RefTypespec* tpcloneRef = s.make<uhdm::RefTypespec>();
                tpcloneRef->setParent(logic_array_tps);
                logic_array_tps->setElemTypespec(tpcloneRef);
              }
              logic_array_tps->getElemTypespec()->setActual(tpclone);
              if (resolution_func) {
                logic_array_tps->setResolutionFunc(resolution_func);
              }
              if (tpclone_typedef != nullptr) {
                tpclone_typedef->getTypedefAlias()->setActual(ts);
              }
              newTypeDef->setTypespec(logic_array_tps);
              dummy->setTypespec(logic_array_tps);
            } else {
              if (ts->getUhdmType() == uhdm::UhdmType::PackedArrayTypespec) {
                tpclone->setInstance(scope->getUhdmModel<uhdm::Instance>());
                tpclone->setName(name);
                if (tpclone_typedef != nullptr) {
                  tpclone_typedef->getTypedefAlias()->setActual(ts);
                }
                if (resolution_func) {
                  if (tpclone->getUhdmType() == uhdm::UhdmType::BitTypespec) {
                    uhdm::BitTypespec* btps = (uhdm::BitTypespec*)tpclone;
                    btps->setResolutionFunc(resolution_func);
                  } else if (tpclone->getUhdmType() ==
                             uhdm::UhdmType::LogicTypespec) {
                    uhdm::LogicTypespec* btps = (uhdm::LogicTypespec*)tpclone;
                    btps->setResolutionFunc(resolution_func);
                  } else if (tpclone->getUhdmType() ==
                             uhdm::UhdmType::StructTypespec) {
                    uhdm::StructTypespec* btps = (uhdm::StructTypespec*)tpclone;
                    btps->setResolutionFunc(resolution_func);
                  }
                }
                newTypeDef->setTypespec(tpclone);
                dummy->setTypespec(tpclone);
              } else {
                packed_array_tps->setInstance(
                    scope->getUhdmModel<uhdm::Instance>());
                packed_array_tps->setName(name);
                if (packed_array_tps->getElemTypespec() == nullptr) {
                  uhdm::RefTypespec* tpcloneRef = s.make<uhdm::RefTypespec>();
                  tpcloneRef->setParent(packed_array_tps);
                  packed_array_tps->setElemTypespec(tpcloneRef);
                }
                packed_array_tps->getElemTypespec()->setActual(tpclone);
                if (tpclone_typedef != nullptr) {
                  tpclone_typedef->getTypedefAlias()->setActual(ts);
                }
                if (resolution_func) {
                  packed_array_tps->setResolutionFunc(resolution_func);
                }
                newTypeDef->setTypespec(packed_array_tps);
                dummy->setTypespec(packed_array_tps);
              }
            }
          } else {
            tpclone->setInstance(scope->getUhdmModel<uhdm::Instance>());
            tpclone->setName(name);
            if (tpclone_typedef != nullptr) {
              tpclone_typedef->getTypedefAlias()->setActual(ts);
            }
            if (resolution_func) {
              if (tpclone->getUhdmType() == uhdm::UhdmType::BitTypespec) {
                uhdm::BitTypespec* btps = (uhdm::BitTypespec*)tpclone;
                btps->setResolutionFunc(resolution_func);
              } else if (tpclone->getUhdmType() ==
                         uhdm::UhdmType::LogicTypespec) {
                uhdm::LogicTypespec* btps = (uhdm::LogicTypespec*)tpclone;
                btps->setResolutionFunc(resolution_func);
              } else if (tpclone->getUhdmType() ==
                         uhdm::UhdmType::StructTypespec) {
                uhdm::StructTypespec* btps = (uhdm::StructTypespec*)tpclone;
                btps->setResolutionFunc(resolution_func);
              }
            }
            newTypeDef->setTypespec(tpclone);
            dummy->setTypespec(tpclone);
          }
        }
      } else {
        dummy->setUnpackedTypespec(array_tps);
      }

      if (scope) scope->insertTypeDef(newTypeDef);
      newType = newTypeDef;
    } else {
      TypeDef* newTypeDef = new TypeDef(fC, type_declaration, stype, name);
      type->setDefinition(newTypeDef);
      if (scope) scope->insertTypeDef(newTypeDef);
      SimpleType* simple = new SimpleType(fC, type_name, stype);
      newTypeDef->setDataType(simple);
      newTypeDef->setDefinition(simple);
      if (uhdm::Typespec* ts = compileTypespec(scope, fC, stype, compileDesign,
                                               reduce, pstmt, nullptr, false)) {
        if (array_tps) {
          if (array_tps->getElemTypespec() == nullptr) {
            uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
            tsRef->setParent(array_tps);
            fC->populateCoreMembers(stype, InvalidNodeId, tsRef);
            tsRef->setEndLine(ts->getEndLine());
            tsRef->setEndColumn(ts->getEndColumn());
            array_tps->setElemTypespec(tsRef);
          }
          array_tps->getElemTypespec()->setActual(ts);
          ts = array_tps;
        }
        if (resolution_func) {
          if (ts->getUhdmType() == uhdm::UhdmType::BitTypespec) {
            uhdm::BitTypespec* btps = (uhdm::BitTypespec*)ts;
            btps->setResolutionFunc(resolution_func);
          } else if (ts->getUhdmType() == uhdm::UhdmType::LogicTypespec) {
            uhdm::LogicTypespec* btps = (uhdm::LogicTypespec*)ts;
            btps->setResolutionFunc(resolution_func);
          } else if (ts->getUhdmType() == uhdm::UhdmType::StructTypespec) {
            uhdm::StructTypespec* btps = (uhdm::StructTypespec*)ts;
            btps->setResolutionFunc(resolution_func);
          } else if (ts->getUhdmType() == uhdm::UhdmType::RealTypespec) {
            uhdm::RealTypespec* btps = (uhdm::RealTypespec*)ts;
            btps->setResolutionFunc(resolution_func);
          }
        }

        if ((m_reduce == Reduce::Yes) && (reduce == Reduce::Yes) &&
            (valuedcomponenti_cast<Package>(scope))) {
          ts->setInstance(scope->getUhdmModel<uhdm::Instance>());
        }
        ts->setName(name);
        simple->setTypespec(ts);
      }
      newType = newTypeDef;
    }
  }

  return newType;
}

bool CompileHelper::compileScopeBody(Scope* parent, Statement* parentStmt,
                                     const FileContent* fC,
                                     NodeId function_statement_or_null) {
  bool result = true;
  while (function_statement_or_null) {
    VObjectType nodeType = fC->Type(function_statement_or_null);
    switch (nodeType) {
      case VObjectType::paFunction_statement_or_null:
      case VObjectType::paStatement_or_null: {
        NodeId statement = fC->Child(function_statement_or_null);
        NodeId statement_item = fC->Child(statement);
        NodeId item = fC->Child(statement_item);
        VObjectType stmtType = fC->Type(item);
        switch (stmtType) {
          case VObjectType::paSubroutine_call_statement: {
            compileSubroutine_call(parent, parentStmt, fC, item);
            break;
          }
          case VObjectType::paSeq_block:
            compileSeqBlock_stmt(parent, parentStmt, fC, item);
            break;
          case VObjectType::paLoop_statement:
            compileLoop_stmt(parent, parentStmt, fC, item);
            break;
          default:  // stmtType
            break;
        }
        break;
      }
      case VObjectType::paStatement: {
        NodeId statement = function_statement_or_null;
        NodeId statement_item = fC->Child(statement);
        NodeId item = fC->Child(statement_item);
        VObjectType stmtType = fC->Type(item);
        switch (stmtType) {
          case VObjectType::paSubroutine_call_statement: {
            compileSubroutine_call(parent, parentStmt, fC, item);
            break;
          }
          case VObjectType::paSeq_block:
            compileSeqBlock_stmt(parent, parentStmt, fC, item);
            break;
          case VObjectType::paLoop_statement:
            compileLoop_stmt(parent, parentStmt, fC, item);
            break;
          default:  // stmtType
            break;
        }
        break;
      } break;
      case VObjectType::paBlock_item_declaration:
        compileScopeVariable(parent, fC, function_statement_or_null);
        break;
      case VObjectType::paSuper_dot_new: {
        NodeId list_of_arguments = fC->Sibling(function_statement_or_null);
        NodeId expression = fC->Child(list_of_arguments);
        std::vector<SubRoutineArg*> args;
        while (expression) {
          SubRoutineArg* arg = new SubRoutineArg(expression, nullptr);
          args.emplace_back(arg);
          expression = fC->Sibling(expression);
        }
        std::vector<NodeId> var_chain;
        var_chain.emplace_back(function_statement_or_null);
        SubRoutineCallStmt* stmt = new SubRoutineCallStmt(
            parent, parentStmt, fC, function_statement_or_null,
            VObjectType::paSubroutine_call_statement, var_chain, "new", args,
            false, false);
        parent->addStmt(stmt);
        if (parentStmt) parentStmt->addStatement(stmt);
        break;
      }
      default:
        break;
    }
    function_statement_or_null = fC->Sibling(function_statement_or_null);
  }

  return result;
}

bool CompileHelper::compileSubroutine_call(Scope* parent, Statement* parentStmt,
                                           const FileContent* fC,
                                           NodeId subroutine_call_statement) {
  /*
  n<d> u<44> t<StringConst> p<48> s<45> l<15>
  n<> u<45> t<Constant_bit_select> p<48> s<46> l<15>
  n<get_current_item> u<46> t<StringConst> p<48> s<47> l<15>
  n<> u<47> t<List_of_arguments> p<48> l<15>
  n<> u<48> t<Subroutine_call> p<49> c<44> l<15>
  n<> u<49> t<Subroutine_call_statement> p<50> c<48> l<15>
  n<> u<50> t<Statement_item> p<51> c<49> l<15>
  n<> u<51> t<Statement> p<52> c<50> l<15>
  n<> u<52> t<Function_statement_or_null> p<61> c<51> s<59> l<15>
  n<foo> u<53> t<StringConst> p<55> s<54> l<16>
  n<> u<54> t<List_of_arguments> p<55> l<16>
  n<> u<55> t<Subroutine_call> p<56> c<53> l<16>
  n<> u<56> t<Subroutine_call_statement> p<57> c<55> l<16>
  n<> u<57> t<Statement_item> p<58> c<56> l<16>
  n<> u<58> t<Statement> p<59> c<57> l<16>
  n<> u<59> t<Function_statement_or_null> p<61> c<58> s<60> l<16>
   */
  std::vector<NodeId> var_chain;
  NodeId subroutine_call = fC->Child(subroutine_call_statement);
  NodeId base_name = fC->Child(subroutine_call);
  NodeId next_name = base_name;
  bool static_call = false;
  bool system_call = false;
  if (fC->Type(base_name) == VObjectType::paDollar_keyword) {
    // system calls
    base_name = fC->Sibling(base_name);
    next_name = base_name;
    system_call = true;
  } else if (fC->Type(base_name) == VObjectType::paImplicit_class_handle) {
    next_name = fC->Sibling(base_name);
    base_name = fC->Child(base_name);
    var_chain.emplace_back(base_name);
  } else if (fC->Type(base_name) == VObjectType::paClass_scope) {
    next_name = fC->Sibling(base_name);
    base_name = fC->Child(base_name);
    base_name = fC->Child(base_name);
    while (base_name) {
      VObjectType ntype = fC->Type(base_name);
      if (ntype == VObjectType::paParameter_value_assignment) {
        base_name = fC->Sibling(base_name);
      }
      if (!base_name) break;
      var_chain.emplace_back(base_name);
      base_name = fC->Sibling(base_name);
    }
    static_call = true;
  }
  while (next_name) {
    VObjectType ntype = fC->Type(next_name);
    if (ntype == VObjectType::paConstant_bit_select) {
      next_name = fC->Sibling(next_name);
    }
    if (ntype == VObjectType::paSelect) {
      next_name = fC->Sibling(next_name);
    }
    if (!next_name) break;
    if (ntype == VObjectType::paList_of_arguments) {
      break;
    }
    var_chain.emplace_back(next_name);

    next_name = fC->Sibling(next_name);
  }
  const std::string_view funcName =
      fC->SymName(var_chain[var_chain.size() - 1]);
  var_chain.pop_back();

  NodeId list_of_arguments = next_name;
  NodeId expression = fC->Child(list_of_arguments);
  std::vector<SubRoutineArg*> args;
  while (expression) {
    SubRoutineArg* arg = new SubRoutineArg(expression, nullptr);
    args.emplace_back(arg);
    expression = fC->Sibling(expression);
  }

  SubRoutineCallStmt* stmt = new SubRoutineCallStmt(
      parent, parentStmt, fC, subroutine_call,
      VObjectType::paSubroutine_call_statement, var_chain, funcName, args,
      static_call, system_call);
  parent->addStmt(stmt);
  if (parentStmt) parentStmt->addStatement(stmt);
  return true;
}

bool CompileHelper::compileSeqBlock_stmt(Scope* parent, Statement* parentStmt,
                                         const FileContent* fC,
                                         NodeId seq_block) {
  NodeId item = fC->Child(seq_block);
  std::string name;
  SeqBlock* block = new SeqBlock(name, parent, parentStmt, fC, seq_block);
  parent->addScope(block);
  parent->addStmt(block);
  if (parentStmt) parentStmt->addStatement(block);
  compileScopeBody(block, block, fC, item);
  return true;
}

bool CompileHelper::compileLoop_stmt(Scope* parent, Statement* parentStmt,
                                     const FileContent* fC,
                                     NodeId loop_statement) {
  NodeId loop = fC->Child(loop_statement);
  switch (fC->Type(loop)) {
    case VObjectType::paFOR:
      compileForLoop_stmt(parent, parentStmt, fC, fC->Sibling(loop));
      break;
    case VObjectType::paFOREACH:
      compileForeachLoop_stmt(parent, parentStmt, fC, fC->Sibling(loop));
      break;
    default:
      break;
  }
  return true;
}

bool CompileHelper::compileForeachLoop_stmt(
    Scope* parent, Statement* parentStmt, const FileContent* fC,
    NodeId ps_or_hierarchical_array_identifier) {
  NodeId loop_variables = fC->Sibling(ps_or_hierarchical_array_identifier);
  NodeId statement = fC->Sibling(loop_variables);
  ForeachLoopStmt* stmt = new ForeachLoopStmt(
      "", fC->Child(ps_or_hierarchical_array_identifier), parent, parentStmt,
      fC, ps_or_hierarchical_array_identifier,
      VObjectType::paPs_or_hierarchical_array_identifier);
  parent->addStmt(stmt);
  parent->addScope(stmt);
  loop_variables = fC->Child(loop_variables);
  while (loop_variables) {
    stmt->addIteratorId(loop_variables);
    loop_variables = fC->Sibling(loop_variables);
  }
  if (parentStmt) parentStmt->addStatement(stmt);
  compileScopeBody(parent, stmt, fC, statement);

  return true;
}

bool CompileHelper::compileForLoop_stmt(Scope* parent, Statement* parentStmt,
                                        const FileContent* fC,
                                        NodeId first_node) {
  VObjectType init_type = fC->Type(first_node);
  NodeId for_initialization;
  NodeId expression;
  NodeId for_step;
  NodeId statement_or_null;
  NodeId itr_data_type;
  ForLoopStmt* stmt = nullptr;
  if (init_type == VObjectType::paStatement_or_null) {
    // for ( ; ; )
    statement_or_null = first_node;
    stmt = new ForLoopStmt("", parent, parentStmt, fC, first_node,
                           VObjectType::paStatement_or_null);
  } else if (init_type == VObjectType::paFor_initialization) {
    // for ( int32_t i = 0; xxx ; xxx )
    for_initialization = first_node;
    expression = fC->Sibling(for_initialization);
    if (fC->Type(expression) == VObjectType::paExpression)
      for_step = fC->Sibling(expression);
    else {
      for_step = expression;
      expression = InvalidNodeId;
    }
    if (fC->Type(for_step) == VObjectType::paFor_step)
      statement_or_null = fC->Sibling(for_step);
    else {
      statement_or_null = for_step;
      for_step = InvalidNodeId;
    }
    stmt = new ForLoopStmt("", parent, parentStmt, fC, for_initialization,
                           VObjectType::paFor_initialization);
    NodeId for_variable_declaration = fC->Child(for_initialization);
    if (for_variable_declaration)
      itr_data_type = fC->Child(for_variable_declaration);
    NodeId the_data_type = fC->Child(itr_data_type);
    VObjectType the_type = fC->Type(the_data_type);
    stmt->setIteratorType(the_type);
  } else if (init_type == VObjectType::paExpression) {
    // for ( ; i < 1 ; xxx )
    expression = first_node;
    for_step = fC->Sibling(expression);
    if (fC->Type(for_step) == VObjectType::paFor_step)
      statement_or_null = fC->Sibling(for_step);
    else {
      statement_or_null = for_step;
      for_step = InvalidNodeId;
    }
    stmt = new ForLoopStmt("", parent, parentStmt, fC, first_node,
                           VObjectType::paExpression);
  }
  parent->addStmt(stmt);
  parent->addScope(stmt);

  if (expression) stmt->setConditionId(expression);

  if (itr_data_type) {
    NodeId iterator = fC->Sibling(itr_data_type);
    while (iterator) {
      NodeId expression = fC->Sibling(iterator);
      if (expression) {
        stmt->addIteratorId(iterator, expression);
        iterator = fC->Sibling(expression);
      } else {
        stmt->addIteratorId(iterator, InvalidNodeId);
        break;
      }
    }
  }

  if (for_step) {
    NodeId for_step_assignment = fC->Child(for_step);
    while (for_step_assignment) {
      NodeId incr = fC->Child(for_step_assignment);
      stmt->addIteratorStepId(incr);
      for_step_assignment = fC->Sibling(for_step_assignment);
    }
  }

  if (parentStmt) parentStmt->addStatement(stmt);
  compileScopeBody(parent, stmt, fC, statement_or_null);

  return true;
}

bool CompileHelper::compileScopeVariable(Scope* parent, const FileContent* fC,
                                         NodeId id) {
  NodeId data_declaration = fC->Child(id);
  NodeId var_decl = fC->Child(data_declaration);
  VObjectType type = fC->Type(data_declaration);
  if (type == VObjectType::paData_declaration) {
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
    if (var_type == VObjectType::paLifetime_Static) {
      var_decl = fC->Sibling(var_decl);
      var_type = fC->Type(var_decl);
    }
    if (var_type == VObjectType::paVariable_declaration) {
      NodeId data_type = fC->Child(var_decl);
      NodeId node_type = fC->Child(data_type);
      VObjectType the_type = fC->Type(node_type);
      std::string typeName;
      if (the_type == VObjectType::slStringConst) {
        typeName = fC->SymName(node_type);
      } else if (the_type == VObjectType::paClass_scope) {
        NodeId class_type = fC->Child(node_type);
        NodeId class_name = fC->Child(class_type);
        typeName = fC->SymName(class_name);
        typeName += "::";
        NodeId symb_id = fC->Sibling(node_type);
        typeName += fC->SymName(symb_id);
      } else {
        typeName = VObject::getTypeName(the_type);
      }
      DataType* datatype = parent->getUsedDataType(typeName);
      if (!datatype) {
        DataType* type =
            new DataType(fC, node_type, typeName, fC->Type(node_type));
        parent->insertUsedDataType(typeName, type);
        datatype = parent->getUsedDataType(typeName);
      }

      NodeId list_of_variable_decl_assignments = fC->Sibling(data_type);
      NodeId variable_decl_assignment =
          fC->Child(list_of_variable_decl_assignments);
      while (variable_decl_assignment) {
        NodeId var = fC->Child(variable_decl_assignment);
        VObjectType varType = fC->Type(var);
        NodeId range = fC->Sibling(var);
        if (varType == VObjectType::paList_of_arguments) {
          // new ()
        } else {
          const std::string_view varName = fC->SymName(var);

          Variable* previous = parent->getVariable(varName);
          if (previous) {
            Location loc1(fC->getFileId(var), fC->Line(var), fC->Column(var),
                          m_session->getSymbolTable()->registerSymbol(varName));
            const FileContent* prevFile = previous->getFileContent();
            NodeId prevNode = previous->getNodeId();
            Location loc2(prevFile->getFileId(prevNode),
                          prevFile->Line(prevNode), prevFile->Column(prevNode),
                          m_session->getSymbolTable()->registerSymbol(varName));
            m_session->getErrorContainer()->addError(
                ErrorDefinition::COMP_MULTIPLY_DEFINED_VARIABLE, loc1, loc2);
          }

          Variable* variable = new Variable(datatype, fC, var, range, varName);
          parent->addVariable(variable);
        }

        variable_decl_assignment = fC->Sibling(variable_decl_assignment);
      }
    } else if (var_type == VObjectType::paType_declaration) {
      // compile_type_declaration_(fC, var_decl);
    }
  }

  return true;
}

VObjectType getSignalType(const FileContent* fC, NodeId net_port_type,
                          NodeId& Packed_dimension, bool& is_signed,
                          bool& is_var, NodeId& nodeType) {
  Packed_dimension = InvalidNodeId;
  is_signed = false;
  is_var = false;
  VObjectType signal_type = VObjectType::paData_type_or_implicit;
  if (net_port_type) {
    NodeId data_type_or_implicit = fC->Child(net_port_type);
    VObjectType the_type = fC->Type(data_type_or_implicit);
    if (the_type == VObjectType::paNetType_Wire ||
        the_type == VObjectType::paNetType_Wand ||
        the_type == VObjectType::paNetType_Uwire ||
        the_type == VObjectType::paNetType_Wor ||
        the_type == VObjectType::paNetType_Tri ||
        the_type == VObjectType::paNetType_TriAnd ||
        the_type == VObjectType::paNetType_TriOr ||
        the_type == VObjectType::paNetType_Tri1 ||
        the_type == VObjectType::paNetType_Tri0 ||
        the_type == VObjectType::paNetType_TriReg ||
        the_type == VObjectType::paNetType_Supply0 ||
        the_type == VObjectType::paNetType_Supply1 ||
        the_type == VObjectType::paImplicit_data_type) {
      signal_type = the_type;
      if (the_type == VObjectType::paImplicit_data_type) {
        // Interconnect
        Packed_dimension = fC->Child(data_type_or_implicit);
        if (fC->Type(Packed_dimension) == VObjectType::paSigning_Signed) {
          is_signed = true;
        }
        if (fC->Type(Packed_dimension) != VObjectType::paPacked_dimension) {
          Packed_dimension = InvalidNodeId;
        }
      }
      data_type_or_implicit = fC->Sibling(data_type_or_implicit);
      if (data_type_or_implicit) {
        Packed_dimension = fC->Child(data_type_or_implicit);
      }
    }
    NodeId data_type = fC->Child(data_type_or_implicit);
    if (data_type) {
      VObjectType the_type = fC->Type(data_type);
      if (the_type == VObjectType::paVar_type) {
        is_var = true;
        data_type_or_implicit = fC->Sibling(data_type);
        data_type = fC->Child(data_type_or_implicit);
        if (data_type)
          the_type = fC->Type(data_type);
        else
          nodeType = data_type_or_implicit;
      }
      if (the_type == VObjectType::paData_type) {
        NodeId integer_vector_type = fC->Child(data_type);
        the_type = fC->Type(integer_vector_type);
        if (the_type == VObjectType::paIntVec_TypeBit ||
            the_type == VObjectType::paIntVec_TypeLogic ||
            the_type == VObjectType::paIntVec_TypeReg ||
            the_type == VObjectType::slStringConst ||
            the_type == VObjectType::paClass_scope ||
            the_type == VObjectType::paIntegerAtomType_Int ||
            the_type == VObjectType::paIntegerAtomType_Integer ||
            the_type == VObjectType::paIntegerAtomType_Shortint ||
            the_type == VObjectType::paIntegerAtomType_LongInt ||
            the_type == VObjectType::paIntegerAtomType_Byte ||
            the_type == VObjectType::paString_type) {
          if (the_type == VObjectType::paIntegerAtomType_Int ||
              the_type == VObjectType::paIntegerAtomType_Shortint ||
              the_type == VObjectType::paIntegerAtomType_LongInt ||
              the_type == VObjectType::paIntegerAtomType_Byte ||
              the_type == VObjectType::paIntegerAtomType_Integer) {
            is_signed = true;
          }

          if (the_type == VObjectType::slStringConst) {
            const std::string_view tname = fC->SymName(integer_vector_type);
            if (tname == "logic") {
              the_type = VObjectType::paIntVec_TypeLogic;
            } else if (tname == "bit") {
              the_type = VObjectType::paIntVec_TypeBit;
            } else if (tname == "byte") {
              the_type = VObjectType::paIntegerAtomType_Byte;
              is_signed = true;
            }
          }
          signal_type = the_type;
          nodeType = integer_vector_type;
          if (the_type != VObjectType::paClass_scope)
            Packed_dimension = fC->Sibling(integer_vector_type);
          else
            Packed_dimension = fC->Sibling(fC->Sibling(integer_vector_type));
        }
      } else if (the_type == VObjectType::paSigning_Signed) {
        Packed_dimension = fC->Sibling(data_type);
        is_signed = true;
      } else if (the_type == VObjectType::paSigning_Unsigned) {
        Packed_dimension = fC->Sibling(data_type);
        is_signed = false;
      } else if (the_type == VObjectType::paPacked_dimension) {
        Packed_dimension = data_type;
      }

      if (fC->Type(Packed_dimension) == VObjectType::paSigning_Signed) {
        Packed_dimension = fC->Sibling(Packed_dimension);
        is_signed = true;
      } else if (fC->Type(Packed_dimension) ==
                 VObjectType::paSigning_Unsigned) {
        Packed_dimension = fC->Sibling(Packed_dimension);
        is_signed = false;
      }
    }
  }
  return signal_type;
}

void setDirectionAndType(DesignComponent* component, const FileContent* fC,
                         NodeId signal, VObjectType type,
                         VObjectType signal_type, NodeId packed_dimension,
                         bool is_signed, bool is_var, NodeId nodeType,
                         uhdm::AttributeCollection* attributes,
                         uhdm::Serializer& s) {
  ModuleDefinition* module =
      valuedcomponenti_cast<ModuleDefinition*>(component);
  VObjectType dir_type = VObjectType::slNoType;
  if (type == VObjectType::paInput_declaration)
    dir_type = VObjectType::paPortDir_Inp;
  else if (type == VObjectType::paOutput_declaration)
    dir_type = VObjectType::paPortDir_Out;
  else if (type == VObjectType::paInout_declaration)
    dir_type = VObjectType::paPortDir_Inout;

  if (module) {
    while (signal) {
      bool found = false;
      for (Signal* port : module->getPorts()) {
        if (port->getName() == fC->SymName(signal)) {
          found = true;
          port->setStatic();
          port->setNetNodeId(fC->Parent(signal));
          port->setNetNameId(signal);
          component->addSignal(port);
          if (is_signed) port->setSigned();
          NodeId unpacked_dimension = fC->Sibling(signal);
          if (fC->Type(unpacked_dimension) ==
              VObjectType::paUnpacked_dimension) {
            port->setUnpackedDimension(unpacked_dimension);
          }
          if (fC->Type(unpacked_dimension) ==
              VObjectType::paConstant_expression) {
            port->setDefaultValue(unpacked_dimension);
          }
          if (attributes) port->attributes(attributes);
          port->setPackedDimension(packed_dimension);
          port->setDirection(dir_type);
          if (signal_type != VObjectType::paData_type_or_implicit) {
            port->setType(signal_type);
          }
          if (nodeType) {
            port->setTypespecId(nodeType);
          }
          if (is_var) port->setVar();
          break;
        }
      }
      if (found == false) {
        Signal* sig =
            new Signal(component, fC, fC->Parent(signal), signal, signal_type,
                       dir_type, packed_dimension,
                       /* unpackedDimension */ InvalidNodeId, is_signed);
        sig->uhdmScopeModel(s.topScope());
        sig->setStatic();
        sig->setTypespecId(nodeType);
        if (is_var) sig->setVar();
        if (attributes) sig->attributes(attributes);
        component->addPort(sig);
        component->addSignal(sig);
      }
      signal = fC->Sibling(signal);

      while (fC->Type(signal) == VObjectType::paVariable_dimension) {
        signal = fC->Sibling(signal);
      }

      if (fC->Type(signal) == VObjectType::paConstant_expression) {
        signal = fC->Sibling(signal);
      }

      if (fC->Type(signal) == VObjectType::paUnpacked_dimension) {
        break;
      }
    }
    return;
  }
  Program* program = valuedcomponenti_cast<Program>(component);
  if (program) {
    while (signal) {
      for (auto& port : program->getPorts()) {
        if (port->getName() == fC->SymName(signal)) {
          port->setDirection(dir_type);
          if (signal_type != VObjectType::paData_type_or_implicit)
            port->setType(signal_type);
          break;
        }
      }
      signal = fC->Sibling(signal);
    }
  }
}

bool CompileHelper::compilePortDeclaration(DesignComponent* component,
                                           const FileContent* fC, NodeId id,
                                           CompileDesign* compileDesign,
                                           VObjectType& port_direction,
                                           bool hasNonNullPort) {
  VObjectType type = fC->Type(id);
  switch (type) {
    case VObjectType::paPort: {
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
        n<> u<12> t<uhdm::Port> p<13> c<11> l<1>
       */

      NodeId Port_expression = fC->Child(id);
      if (Port_expression &&
          (fC->Type(Port_expression) == VObjectType::paPort_expression)) {
        NodeId if_type = fC->Child(Port_expression);
        if (fC->Type(if_type) == VObjectType::paPort_reference) {
          NodeId if_type_name_s = fC->Child(if_type);
          NodeId if_name = fC->Sibling(if_type);
          if (if_name) {
            NodeId if_name_s = fC->Child(if_name);
            Signal* signal = new Signal(
                component, fC, Port_expression, if_name_s, if_type_name_s,
                VObjectType::slNoType, InvalidNodeId, false);
            signal->uhdmScopeModel(compileDesign->getSerializer().topScope());
            signal->setStatic();
            component->addPort(signal);
          } else {
            Signal* signal =
                new Signal(component, fC, Port_expression, if_type_name_s,
                           VObjectType::paData_type_or_implicit, port_direction,
                           InvalidNodeId, InvalidNodeId, false);
            signal->uhdmScopeModel(compileDesign->getSerializer().topScope());
            signal->setStatic();
            component->addPort(signal);
          }
        }
      } else {
        if (hasNonNullPort) {
          // Null port
          Signal* signal = new Signal(
              component, fC, id, id, VObjectType::slNoType,
              VObjectType::slNoType, InvalidNodeId, InvalidNodeId, false);
          signal->uhdmScopeModel(compileDesign->getSerializer().topScope());
          signal->setStatic();
          component->addPort(signal);
        }
      }
      break;
    }
    case VObjectType::paPort_declaration: {
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
      uhdm::AttributeCollection* attributes = nullptr;
      if (subType == VObjectType::paAttribute_instance) {
        attributes =
            compileAttributes(component, fC, subNode, compileDesign, nullptr);
        while (fC->Type(subNode) == VObjectType::paAttribute_instance) {
          subNode = fC->Sibling(subNode);
          subType = fC->Type(subNode);
        }
      }
      switch (subType) {
        case VObjectType::paInterface_port_declaration: {
          /*
          n<DD2> u<12> t<StringConst> p<13> l<16>
          n<> u<13> t<Interface_identifier> p<17> c<12> s<16> l<16>
          n<toto2> u<14> t<StringConst> p<15> l<16>
          n<> u<15> t<Interface_identifier> p<16> c<14> l<16>
          n<> u<16> t<List_of_interface_identifiers> p<17> c<15> l<16>
          n<> u<17> t<Interface_port_declaration> p<18> c<13> l<16>
          n<> u<18> t<Port_declaration> p<19> c<17> l<16>
          */
          NodeId type_identifier = fC->Child(subNode);
          NodeId interfIdName = fC->Child(type_identifier);

          NodeId list_of_interface_identifiers = fC->Sibling(type_identifier);
          NodeId interface_identifier =
              fC->Child(list_of_interface_identifiers);
          while (interface_identifier) {
            NodeId identifier = fC->Child(interface_identifier);
            NodeId Unpacked_dimension = fC->Sibling(interface_identifier);
            NodeId unpackedDimension;
            if (fC->Type(Unpacked_dimension) ==
                VObjectType::paUnpacked_dimension) {
              interface_identifier = fC->Sibling(interface_identifier);
              unpackedDimension = Unpacked_dimension;
            }
            Signal* signal = new Signal(
                component, fC, interface_identifier, identifier, interfIdName,
                VObjectType::slNoType, unpackedDimension, false);
            signal->uhdmScopeModel(compileDesign->getSerializer().topScope());
            signal->setStatic();
            component->addSignal(signal);
            interface_identifier = fC->Sibling(interface_identifier);
            while (interface_identifier &&
                   (fC->Type(interface_identifier) ==
                    VObjectType::paUnpacked_dimension)) {
              interface_identifier = fC->Sibling(interface_identifier);
            }
          }
          break;
        }
        case VObjectType::paAttribute_instance:
          /* module dff0_test(n1);
              (* init = 32'd1 *)
              output n1; */
          subNode = fC->Sibling(subNode);
          subType = fC->Type(subNode);
          [[fallthrough]];
        case VObjectType::paInput_declaration:
        case VObjectType::paOutput_declaration:
        case VObjectType::paInout_declaration: {
          /*
            n<> u<24> t<Data_type_or_implicit> p<25> l<7>
            n<> u<25> t<Net_port_type> p<28> c<24> s<27> l<7>
            n<c0> u<26> t<StringConst> p<27> l<7>
            n<> u<27> t<List_of_port_identifiers> p<28> c<26> l<7>
            n<> u<28> t<Output_declaration> p<29> c<25> l<7>
           */
          NodeId net_port_type = fC->Child(subNode);
          NodeId Packed_dimension;
          bool is_signed = false;
          bool is_var = false;
          NodeId nodeType;
          VObjectType signal_type = getSignalType(
              fC, net_port_type, /*ref*/ Packed_dimension,
              /*ref*/ is_signed, /*ref*/ is_var, /*ref*/ nodeType);
          NodeId list_of_port_identifiers = fC->Sibling(net_port_type);
          if (fC->Type(list_of_port_identifiers) ==
              VObjectType::paPacked_dimension) {
            list_of_port_identifiers = fC->Sibling(list_of_port_identifiers);
          }
          NodeId signal = fC->Child(list_of_port_identifiers);
          if (!nodeType) {
            nodeType = fC->Child(net_port_type);
          }
          setDirectionAndType(component, fC, signal, subType, signal_type,
                              Packed_dimension, is_signed, is_var, nodeType,
                              attributes, compileDesign->getSerializer());
          break;
        }
        default:
          break;
      }
      break;
    }
    default:
      break;
  }
  return true;
}

uhdm::Expr* CompileHelper::exprFromAssign(DesignComponent* component,
                                          CompileDesign* compileDesign,
                                          const FileContent* fC, NodeId id,
                                          NodeId unpackedDimension) {
  // Assignment section
  NodeId assignment;
  NodeId Assign = fC->Sibling(id);
  if (Assign && (fC->Type(Assign) == VObjectType::paExpression)) {
    assignment = Assign;
  }
  if (unpackedDimension) {
    NodeId tmp = unpackedDimension;
    while ((fC->Type(tmp) == VObjectType::paUnpacked_dimension) ||
           (fC->Type(tmp) == VObjectType::paVariable_dimension)) {
      tmp = fC->Sibling(tmp);
    }
    if (tmp && (fC->Type(tmp) != VObjectType::paUnpacked_dimension) &&
        (fC->Type(tmp) != VObjectType::paVariable_dimension)) {
      assignment = tmp;
    }
  }

  NodeId expression;
  if (assignment) {
    if (fC->Type(assignment) == VObjectType::paClass_new) {
      expression = assignment;
    } else {
      NodeId Primary = fC->Child(assignment);
      if (fC->Type(assignment) == VObjectType::paExpression) {
        Primary = assignment;
      }
      expression = Primary;
    }
  } else {
    expression = fC->Sibling(id);
    if ((fC->Type(expression) != VObjectType::paExpression) &&
        (fC->Type(expression) != VObjectType::paConstant_expression))
      expression = InvalidNodeId;
  }

  uhdm::Expr* exp = nullptr;
  if (expression) {
    exp = (uhdm::Expr*)compileExpression(component, fC, expression,
                                         compileDesign, Reduce::No);
  }
  return exp;
}

bool CompileHelper::compileSignal(DesignComponent* comp,
                                  CompileDesign* compileDesign, Signal* sig,
                                  std::string_view prefix, bool signalIsPort,
                                  Reduce reduce) {
  uhdm::Serializer& s = compileDesign->getSerializer();

  uhdm::Any* uhdmScope = sig->uhdmScopeModel();
  if (uhdmScope == nullptr) uhdmScope = comp->getUhdmModel();
  const uhdm::ScopedScope scopedScope(uhdmScope);

  const FileContent* fC = sig->getFileContent();
  NodeId id = sig->getNodeId();
  NodeId packedDimension = sig->getPackedDimension();
  NodeId unpackedDimension = sig->getUnpackedDimension();
  // Nets pass
  const DataType* dtype = sig->getDataType();
  VObjectType subnettype = sig->getType();
  uhdm::Typespec* tps = nullptr;
  // Determine if the "signal" is a net or a var
  bool isNet = true;
  if ((dtype && (subnettype == VObjectType::slNoType)) || sig->isConst() ||
      sig->isVar() || (!sig->isStatic()) ||
      (subnettype == VObjectType::paClass_scope) ||
      (subnettype == VObjectType::slStringConst) ||
      (subnettype == VObjectType::paIntegerAtomType_Int) ||
      (subnettype == VObjectType::paIntegerAtomType_Integer) ||
      (subnettype == VObjectType::paIntegerAtomType_Byte) ||
      (subnettype == VObjectType::paIntegerAtomType_LongInt) ||
      (subnettype == VObjectType::paIntegerAtomType_Shortint) ||
      (subnettype == VObjectType::paString_type) ||
      (subnettype == VObjectType::paNonIntType_Real) ||
      (subnettype == VObjectType::paNonIntType_RealTime) ||
      (subnettype == VObjectType::paNonIntType_ShortReal) ||
      (subnettype == VObjectType::paEvent_type) ||
      (subnettype == VObjectType::paChandle_type) ||
      (subnettype == VObjectType::paIntVec_TypeBit) ||
      (subnettype == VObjectType::paEnum_base_type) ||
      ((!sig->isVar()) && (subnettype == VObjectType::paIntVec_TypeLogic))) {
    isNet = false;
  }
  if (sig->getDirection() == VObjectType::paPortDir_Out ||
      sig->getDirection() == VObjectType::paPortDir_Inp ||
      sig->getDirection() == VObjectType::paPortDir_Inout) {
    if ((!sig->isVar()) && (subnettype == VObjectType::paIntVec_TypeLogic)) {
      isNet = true;
    }
  }

  if (sig->getTypespecId()) {
    checkForLoops(true);
    tps = compileTypespec(comp, fC, sig->getTypespecId(), compileDesign, reduce,
                          uhdmScope, nullptr, true);
    checkForLoops(false);
  }
  if ((tps == nullptr) && sig->getInterfaceTypeNameId()) {
    checkForLoops(true);
    tps = compileTypespec(comp, fC, sig->getInterfaceTypeNameId(),
                          compileDesign, reduce, uhdmScope, nullptr, true);
    checkForLoops(false);
  }
  if (tps) {
    uhdm::Typespec* tmp = tps;
    uhdm::UhdmType ttmp = tmp->getUhdmType();
    if ((tps != nullptr) &&
        (tps->getUhdmType() == uhdm::UhdmType::PackedArrayTypespec)) {
      if (uhdm::RefTypespec* ert =
              ((uhdm::PackedArrayTypespec*)tps)->getElemTypespec()) {
        tmp = ert->getActual();
      }
    } else if (ttmp == uhdm::UhdmType::StructTypespec) {
      uhdm::StructTypespec* the_tps = (uhdm::StructTypespec*)tmp;
      if (the_tps->getMembers()) {
        isNet = true;
        for (uhdm::TypespecMember* member : *the_tps->getMembers()) {
          if (const uhdm::Typespec* mtps = member->getTypespec()->getActual()) {
            uhdm::UhdmType mtype = mtps->getUhdmType();
            if (mtype != uhdm::UhdmType::LogicTypespec &&
                mtype != uhdm::UhdmType::StructTypespec) {
              isNet = false;
              break;
            }
          }
        }
      }
    } else if (ttmp == uhdm::UhdmType::EnumTypespec) {
      isNet = false;
    } else if (ttmp == uhdm::UhdmType::BitTypespec) {
      isNet = false;
    } else if (ttmp == uhdm::UhdmType::ByteTypespec) {
      isNet = false;
    } else if (ttmp == uhdm::UhdmType::RealTypespec) {
      isNet = false;
    } else if (ttmp == uhdm::UhdmType::ClassTypespec) {
      isNet = false;
    } else if (ttmp == uhdm::UhdmType::InterfaceTypespec) {
      if (!signalIsPort) {
        SymbolTable* symbols = m_session->getSymbolTable();
        ErrorContainer* errors = m_session->getErrorContainer();
        Location loc1(fC->getFileId(), fC->Line(id), fC->Column(id),
                      symbols->registerSymbol(sig->getName()));
        errors->addError(ErrorDefinition::ELAB_USE_INTERFACE_AS_SIGNAL_TYPE,
                         loc1);
      }
      // Don't create a signal
      return isNet;
    }
  }

  const std::string_view signame = sig->getName();
  const std::string parentSymbol = StrCat(prefix, signame);
  const NodeId rtBeginId = sig->getInterfaceTypeNameId()
                               ? sig->getInterfaceTypeNameId()
                               : sig->getTypespecId();
  const NodeId rtEndId =
      sig->getPackedDimension() ? sig->getPackedDimension() : rtBeginId;

  // Packed and unpacked ranges
  int32_t packedSize;
  int32_t unpackedSize;
  checkForLoops(true);
  std::vector<uhdm::Range*>* packedDimensions =
      compileRanges(comp, fC, packedDimension, compileDesign, reduce, nullptr,
                    nullptr, packedSize, false);
  checkForLoops(false);
  checkForLoops(true);
  std::vector<uhdm::Range*>* unpackedDimensions =
      compileRanges(comp, fC, unpackedDimension, compileDesign, reduce, nullptr,
                    nullptr, unpackedSize, false);
  checkForLoops(false);
  uhdm::Any* obj = nullptr;

  // Assignment to a default value
  uhdm::Expr* exp =
      exprFromAssign(comp, compileDesign, fC, id, unpackedDimension);
  if ((exp == nullptr) && sig->getDefaultValue()) {
    checkForLoops(true);
    exp =
        (uhdm::Expr*)compileExpression(comp, fC, sig->getDefaultValue(),
                                       compileDesign, reduce, nullptr, nullptr);
    checkForLoops(false);
  }
  if (isNet) {
    // Nets
    if (dtype) {
      dtype = dtype->getActual();
      if (const DummyType* en = datatype_cast<DummyType>(dtype)) {
        uhdm::Typespec* spec = en->getTypespec();
        if (spec->getUhdmType() == uhdm::UhdmType::LogicTypespec) {
          uhdm::LogicNet* logicn = s.make<uhdm::LogicNet>();
          if (sig->attributes()) {
            logicn->setAttributes(sig->attributes());
            for (auto a : *sig->attributes()) a->setParent(logicn);
          }
          logicn->setSigned(sig->isSigned());
          logicn->setNetType(UhdmWriter::getVpiNetType(sig->getType()));
          fC->populateCoreMembers(sig->getNetNameId(), sig->getNetNameId(),
                                  logicn);
          // Move range to typespec for simple types
          // logicn->setRanges(packedDimensions);
          uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
          rt->setParent(logicn);
          rt->setActual(spec);
          fC->populateCoreMembers(rtBeginId, rtEndId, rt);
          logicn->setTypespec(rt);
          logicn->setName(signame);
          spec->setParent(logicn);
          obj = logicn;
        } else if (spec->getUhdmType() == uhdm::UhdmType::StructTypespec) {
          uhdm::StructNet* stv = s.make<uhdm::StructNet>();
          if (sig->attributes()) {
            stv->setAttributes(sig->attributes());
            for (auto a : *sig->attributes()) a->setParent(stv);
          }
          fC->populateCoreMembers(sig->getNetNameId(), sig->getNetNameId(),
                                  stv);
          uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
          rt->setParent(stv);
          rt->setActual(spec);
          fC->populateCoreMembers(rtBeginId, rtEndId, rt);
          stv->setTypespec(rt);
          spec->setParent(stv);
          obj = stv;
          if (packedDimensions) {
            uhdm::PackedArrayNet* pnets = s.make<uhdm::PackedArrayNet>();
            pnets->setRanges(packedDimensions);
            pnets->getElements(true)->emplace_back(stv);
            stv->setParent(pnets);
            for (auto r : *packedDimensions) r->setParent(pnets);
            obj = pnets;
          }
        } else if (spec->getUhdmType() == uhdm::UhdmType::EnumTypespec) {
          uhdm::EnumNet* stv = s.make<uhdm::EnumNet>();
          if (sig->attributes()) {
            stv->setAttributes(sig->attributes());
            for (auto a : *sig->attributes()) a->setParent(stv);
          }
          fC->populateCoreMembers(sig->getNetNameId(), sig->getNetNameId(),
                                  stv);
          uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
          rt->setParent(stv);
          rt->setActual(spec);
          fC->populateCoreMembers(rtBeginId, rtEndId, rt);
          stv->setTypespec(rt);
          spec->setParent(stv);
          obj = stv;
          if (packedDimensions) {
            uhdm::PackedArrayNet* pnets = s.make<uhdm::PackedArrayNet>();
            pnets->setRanges(packedDimensions);
            pnets->getElements(true)->emplace_back(stv);
            stv->setParent(pnets);
            for (auto r : *packedDimensions) r->setParent(pnets);
            obj = pnets;
          }
        } else if (spec->getUhdmType() == uhdm::UhdmType::BitTypespec) {
          uhdm::BitVar* logicn = s.make<uhdm::BitVar>();
          if (sig->attributes()) {
            logicn->setAttributes(sig->attributes());
            for (auto a : *sig->attributes()) a->setParent(logicn);
          }
          logicn->setSigned(sig->isSigned());
          fC->populateCoreMembers(sig->getNetNameId(), sig->getNetNameId(),
                                  logicn);
          // Move range to typespec for simple types
          // logicn->setRanges(packedDimensions);
          uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
          rt->setParent(logicn);
          rt->setActual(spec);
          fC->populateCoreMembers(rtBeginId, rtEndId, rt);
          logicn->setTypespec(rt);
          logicn->setName(signame);
          spec->setParent(logicn);
          obj = logicn;
        } else if (spec->getUhdmType() == uhdm::UhdmType::ByteTypespec) {
          uhdm::ByteVar* logicn = s.make<uhdm::ByteVar>();
          if (sig->attributes()) {
            logicn->setAttributes(sig->attributes());
            for (auto a : *sig->attributes()) a->setParent(logicn);
          }
          fC->populateCoreMembers(sig->getNetNameId(), sig->getNetNameId(),
                                  logicn);
          logicn->setSigned(sig->isSigned());
          logicn->setName(signame);
          uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
          rt->setParent(logicn);
          rt->setActual(spec);
          fC->populateCoreMembers(rtBeginId, rtEndId, rt);
          logicn->setTypespec(rt);
          spec->setParent(logicn);
          obj = logicn;
        } else {
          uhdm::Variables* var = getSimpleVarFromTypespec(
              fC, id, id, spec, packedDimensions, compileDesign);
          if (sig->attributes()) {
            var->setAttributes(sig->attributes());
            for (auto a : *sig->attributes()) a->setParent(var);
          }
          var->setExpr(exp);
          var->setConstantVariable(sig->isConst());
          var->setSigned(sig->isSigned());
          var->setName(signame);
          exp->setParent(var);
          fC->populateCoreMembers(sig->getNetNameId(), sig->getNetNameId(),
                                  var);
          obj = var;
        }
      } else if (const Enum* en = datatype_cast<Enum>(dtype)) {
        uhdm::EnumNet* stv = s.make<uhdm::EnumNet>();
        stv->setName(signame);
        fC->populateCoreMembers(sig->getNetNameId(), sig->getNetNameId(), stv);
        uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
        rt->setParent(stv);
        rt->setActual(en->getTypespec());
        fC->populateCoreMembers(rtBeginId, rtEndId, rt);
        stv->setTypespec(rt);
        if (sig->attributes()) {
          stv->setAttributes(sig->attributes());
          for (auto a : *sig->attributes()) a->setParent(stv);
        }
        obj = stv;
        if (packedDimensions) {
          uhdm::PackedArrayNet* pnets = s.make<uhdm::PackedArrayNet>();
          pnets->setRanges(packedDimensions);
          pnets->getElements(true)->emplace_back(stv);
          stv->setParent(pnets);
          for (auto r : *packedDimensions) r->setParent(pnets);
          obj = pnets;
          pnets->setNetType(UhdmWriter::getVpiNetType(sig->getType()));
        } else {
          stv->setNetType(UhdmWriter::getVpiNetType(sig->getType()));
        }
      } else if (const Struct* st = datatype_cast<Struct>(dtype)) {
        uhdm::StructNet* stv = s.make<uhdm::StructNet>();
        stv->setName(signame);
        if (sig->attributes()) {
          stv->setAttributes(sig->attributes());
          for (auto a : *sig->attributes()) a->setParent(stv);
        }
        fC->populateCoreMembers(sig->getNetNameId(), sig->getNetNameId(), stv);
        uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
        rt->setParent(stv);
        rt->setActual(st->getTypespec());
        fC->populateCoreMembers(rtBeginId, rtEndId, rt);
        stv->setTypespec(rt);
        obj = stv;
        if (packedDimensions) {
          uhdm::PackedArrayNet* pnets = s.make<uhdm::PackedArrayNet>();
          pnets->setRanges(packedDimensions);
          pnets->getElements(true)->emplace_back(stv);
          stv->setParent(pnets);
          for (auto r : *packedDimensions) r->setParent(pnets);
          obj = pnets;
          pnets->setNetType(UhdmWriter::getVpiNetType(sig->getType()));
        } else {
          stv->setNetType(UhdmWriter::getVpiNetType(sig->getType()));
        }
      } else if (dtype->getCategory() == DataType::Category::PARAMETER ||
                 dtype->getCategory() == DataType::Category::SIMPLE_TYPEDEF) {
        uhdm::Typespec* spec = nullptr;
        if (dtype->getCategory() == DataType::Category::SIMPLE_TYPEDEF) {
          const SimpleType* sit = datatype_cast<SimpleType>(dtype);
          spec = sit->getTypespec();
        } else {
          const Parameter* param = datatype_cast<Parameter>(dtype);
          spec = param->getTypespec();
          if (spec == nullptr) {
            spec = tps;
          }
        }
        if (spec->getUhdmType() == uhdm::UhdmType::LogicTypespec) {
          uhdm::LogicNet* logicn = s.make<uhdm::LogicNet>();
          if (sig->attributes()) {
            logicn->setAttributes(sig->attributes());
            for (auto a : *sig->attributes()) a->setParent(logicn);
          }
          logicn->setSigned(sig->isSigned());
          logicn->setNetType(UhdmWriter::getVpiNetType(sig->getType()));
          fC->populateCoreMembers(sig->getNetNameId(), sig->getNetNameId(),
                                  logicn);
          // Move range to typespec for simple types
          // logicn->setRanges(packedDimensions);
          uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
          rt->setParent(logicn);
          rt->setActual(spec);
          fC->populateCoreMembers(rtBeginId, rtEndId, rt);
          logicn->setTypespec(rt);
          spec->setParent(logicn);
          logicn->setName(signame);
          obj = logicn;
        } else if (spec->getUhdmType() == uhdm::UhdmType::StructTypespec) {
          uhdm::StructNet* stv = s.make<uhdm::StructNet>();
          stv->setName(signame);
          if (sig->attributes()) {
            stv->setAttributes(sig->attributes());
            for (auto a : *sig->attributes()) a->setParent(stv);
          }
          fC->populateCoreMembers(sig->getNetNameId(), sig->getNetNameId(),
                                  stv);
          uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
          rt->setParent(stv);
          rt->setActual(spec);
          fC->populateCoreMembers(rtBeginId, rtEndId, rt);
          stv->setTypespec(rt);
          spec->setParent(stv);
          obj = stv;
          if (packedDimensions) {
            uhdm::PackedArrayNet* pnets = s.make<uhdm::PackedArrayNet>();
            pnets->setRanges(packedDimensions);
            pnets->getElements(true)->emplace_back(stv);
            stv->setParent(pnets);
            for (auto r : *packedDimensions) r->setParent(pnets);
            obj = pnets;
            pnets->setNetType(UhdmWriter::getVpiNetType(sig->getType()));
          } else {
            stv->setNetType(UhdmWriter::getVpiNetType(sig->getType()));
          }
        } else if (spec->getUhdmType() == uhdm::UhdmType::EnumTypespec) {
          uhdm::EnumNet* stv = s.make<uhdm::EnumNet>();
          stv->setName(signame);
          if (sig->attributes()) {
            stv->setAttributes(sig->attributes());
            for (auto a : *sig->attributes()) a->setParent(stv);
          }
          fC->populateCoreMembers(sig->getNetNameId(), sig->getNetNameId(),
                                  stv);
          uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
          rt->setParent(stv);
          rt->setActual(spec);
          fC->populateCoreMembers(rtBeginId, rtEndId, rt);
          stv->setTypespec(rt);
          spec->setParent(stv);
          obj = stv;
          if (packedDimensions) {
            uhdm::PackedArrayNet* pnets = s.make<uhdm::PackedArrayNet>();
            pnets->setRanges(packedDimensions);
            pnets->getElements(true)->emplace_back(stv);
            stv->setParent(pnets);
            fC->populateCoreMembers(sig->getNetNameId(), sig->getNetNameId(),
                                    pnets);
            for (auto r : *packedDimensions) r->setParent(pnets);
            obj = pnets;
            pnets->setNetType(UhdmWriter::getVpiNetType(sig->getType()));
          } else {
            stv->setNetType(UhdmWriter::getVpiNetType(sig->getType()));
          }
        } else if (spec->getUhdmType() == uhdm::UhdmType::BitTypespec) {
          uhdm::BitVar* logicn = s.make<uhdm::BitVar>();
          if (sig->attributes()) {
            logicn->setAttributes(sig->attributes());
            for (auto a : *sig->attributes()) a->setParent(logicn);
          }
          logicn->setSigned(sig->isSigned());
          fC->populateCoreMembers(sig->getNetNameId(), sig->getNetNameId(),
                                  logicn);
          uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
          rt->setParent(logicn);
          rt->setActual(spec);
          fC->populateCoreMembers(rtBeginId, rtEndId, rt);
          logicn->setTypespec(rt);
          spec->setParent(logicn);
          // Move range to typespec for simple types
          // logicn->setRanges(packedDimensions);
          logicn->setName(signame);
          obj = logicn;
        } else if (spec->getUhdmType() == uhdm::UhdmType::ByteTypespec) {
          uhdm::ByteVar* logicn = s.make<uhdm::ByteVar>();
          if (sig->attributes()) {
            logicn->setAttributes(sig->attributes());
            for (auto a : *sig->attributes()) a->setParent(logicn);
          }
          logicn->setSigned(sig->isSigned());
          logicn->setName(signame);
          fC->populateCoreMembers(sig->getNetNameId(), sig->getNetNameId(),
                                  logicn);
          uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
          rt->setParent(logicn);
          rt->setActual(spec);
          fC->populateCoreMembers(rtBeginId, rtEndId, rt);
          logicn->setTypespec(rt);
          spec->setParent(logicn);
          obj = logicn;
        } else {
          uhdm::Variables* var = getSimpleVarFromTypespec(
              fC, id, id, spec, packedDimensions, compileDesign);
          if (sig->attributes()) {
            var->setAttributes(sig->attributes());
            for (auto a : *sig->attributes()) a->setParent(var);
          }
          var->setExpr(exp);
          var->setConstantVariable(sig->isConst());
          var->setSigned(sig->isSigned());
          var->setName(signame);
          fC->populateCoreMembers(sig->getNetNameId(), sig->getNetNameId(),
                                  var);
          exp->setParent(var);
          obj = var;
        }
      } else {
        uhdm::LogicNet* logicn = s.make<uhdm::LogicNet>();
        if (sig->attributes()) {
          logicn->setAttributes(sig->attributes());
          for (auto a : *sig->attributes()) a->setParent(logicn);
        }
        logicn->setParent(uhdmScope);
        logicn->setSigned(sig->isSigned());
        logicn->setNetType(UhdmWriter::getVpiNetType(sig->getType()));
        fC->populateCoreMembers(sig->getNetNameId(), sig->getNetNameId(),
                                logicn);
        if (tps != nullptr) {
          uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
          rt->setParent(logicn);
          rt->setActual(tps);
          fC->populateCoreMembers(rtBeginId, rtEndId, rt);
          logicn->setTypespec(rt);
        }
        // Move range to typespec for simple types
        // logicn->setRanges(packedDimensions);
        logicn->setName(signame);
        obj = logicn;
      }

      if (unpackedDimensions) {
        uhdm::ArrayNet* array_net = s.make<uhdm::ArrayNet>();
        array_net->setParent(uhdmScope);
        array_net->setRanges(unpackedDimensions);
        array_net->setName(signame);
        array_net->setSize(unpackedSize);
        for (auto r : *unpackedDimensions) r->setParent(array_net);
        fC->populateCoreMembers(sig->getNetNameId(), sig->getNetNameId(),
                                array_net);
        obj->setParent(array_net);
      } else {
        uhdm::UhdmType nettype = obj->getUhdmType();
        if (nettype == uhdm::UhdmType::EnumNet) {
          ((uhdm::EnumNet*)obj)->setName(signame);
        } else if (nettype == uhdm::UhdmType::StructNet) {
          ((uhdm::StructNet*)obj)->setName(signame);
        } else if (nettype == uhdm::UhdmType::PackedArrayNet) {
          ((uhdm::PackedArrayNet*)obj)->setName(signame);
        }
      }
    } else if (subnettype == VObjectType::paStruct_union) {
      // Implicit type
      uhdm::StructNet* stv = s.make<uhdm::StructNet>();
      stv->setName(signame);
      stv->setParent(uhdmScope);
      fC->populateCoreMembers(sig->getNetNameId(), sig->getNetNameId(), stv);
      if (sig->attributes()) {
        stv->setAttributes(sig->attributes());
        for (auto a : *sig->attributes()) a->setParent(stv);
      }
      if (tps != nullptr) {
        uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
        rt->setParent(stv);
        rt->setActual(tps);
        rt->setName(fC->SymName(sig->getNameId()));
        fC->populateCoreMembers(rtBeginId, rtEndId, rt);
        stv->setTypespec(rt);
      }
      obj = stv;
    } else if (tps && tps->getUhdmType() == uhdm::UhdmType::StructTypespec) {
      uhdm::StructNet* stv = s.make<uhdm::StructNet>();
      stv->setName(signame);
      fC->populateCoreMembers(sig->getNetNameId(), sig->getNetNameId(), stv);
      uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
      rt->setParent(stv);
      rt->setName(fC->SymName(sig->getNameId()));
      fC->populateCoreMembers(rtBeginId, rtEndId, rt);
      rt->setActual(tps);
      stv->setTypespec(rt);
      stv->setParent(uhdmScope);
      obj = stv;
      if (unpackedDimensions) {
        uhdm::ArrayNet* array_net = s.make<uhdm::ArrayNet>();
        array_net->setParent(uhdmScope);
        array_net->setRanges(unpackedDimensions);
        array_net->setName(signame);
        array_net->setSize(unpackedSize);
        for (auto r : *unpackedDimensions) r->setParent(array_net);
        fC->populateCoreMembers(sig->getNetNameId(), sig->getNetNameId(),
                                array_net);
      } else {
        if (obj->getUhdmType() == uhdm::UhdmType::EnumNet) {
          ((uhdm::EnumNet*)obj)->setName(signame);
        } else if (obj->getUhdmType() == uhdm::UhdmType::StructNet) {
          ((uhdm::StructNet*)obj)->setName(signame);
        }
      }
    } else {
      uhdm::LogicNet* logicn = s.make<uhdm::LogicNet>();
      logicn->setSigned(sig->isSigned());
      logicn->setNetType(UhdmWriter::getVpiNetType(sig->getType()));
      logicn->setName(fC->SymName(sig->getNetNameId()));
      fC->populateCoreMembers(sig->getNetNameId(), sig->getNetNameId(), logicn);
      if (sig->attributes()) {
        logicn->setAttributes(sig->attributes());
        for (auto a : *sig->attributes()) a->setParent(logicn);
      }
      if (tps != nullptr) {
        // Move range to typespec for simple types
        // logicn->setRanges(packedDimensions);
        uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
        rt->setParent(logicn);
        rt->setName(tps->getName());
        rt->setActual(tps);
        logicn->setTypespec(rt);
        fC->populateCoreMembers(rtBeginId, rtEndId, rt);
      }
      if (unpackedDimensions) {
        uhdm::ArrayNet* array_net = s.make<uhdm::ArrayNet>();
        array_net->setRanges(unpackedDimensions);
        array_net->setName(signame);
        array_net->setSize(unpackedSize);
        for (auto r : *unpackedDimensions) r->setParent(array_net);
        fC->populateCoreMembers(sig->getNetNameId(), sig->getNetNameId(),
                                array_net);
        logicn->setParent(uhdmScope);
        obj = array_net;
      } else {
        logicn->setName(signame);
        logicn->setSigned(sig->isSigned());
        logicn->setParent(uhdmScope);
        obj = logicn;
      }
    }

    if (exp && (!signalIsPort)) {
      uhdm::ContAssign* assign = s.make<uhdm::ContAssign>();
      assign->setNetDeclAssign(true);
      fC->populateCoreMembers(id, id, assign);
      assign->setLhs((uhdm::Expr*)obj);
      assign->setRhs(exp);
      obj->setParent(assign);
      exp->setParent(assign);
      if (sig->getDelay()) {
        checkForLoops(true);
        if (uhdm::Expr* delay_expr = (uhdm::Expr*)compileExpression(
                comp, fC, sig->getDelay(), compileDesign, reduce, assign,
                nullptr)) {
          assign->setDelay(delay_expr);
        }
        checkForLoops(false);
      }
    }
  } else {
    // Vars
    obj =
        compileVariable(comp, compileDesign, sig, packedDimensions, packedSize,
                        unpackedDimensions, unpackedSize, exp, tps);
    if (exp != nullptr) exp->setParent(obj, true);
  }

  if (obj) {
    fC->populateCoreMembers(sig->getNameId(), sig->getNameId(), obj);
  } else {
    // Unsupported type
    ErrorContainer* errors = m_session->getErrorContainer();
    SymbolTable* symbols = m_session->getSymbolTable();
    Location loc(fC->getFileId(), fC->Line(id), fC->Column(id),
                 symbols->registerSymbol(signame));
    errors->addError(ErrorDefinition::UHDM_UNSUPPORTED_SIGNAL, loc);
  }
  return isNet;
}

bool CompileHelper::compileAnsiPortDeclaration(DesignComponent* component,
                                               const FileContent* fC, NodeId id,
                                               CompileDesign* compileDesign,
                                               VObjectType& port_direction) {
  /*
  n<mem_if> u<3> t<StringConst> p<4> l<11>
  n<> u<4> t<Data_type> p<5> c<3> l<11>
  n<> u<5> t<Data_type_or_implicit> p<6> c<4> l<11>
  n<> u<6> t<Net_port_type> p<7> c<5> l<11>
  n<> u<7> t<Net_port_header> p<9> c<6> s<8> l<11>
  n<sif1> u<8> t<StringConst> p<9> l<11>
  n<> u<9> t<Ansi_port_declaration> p<16> c<7> s<15> l<11>

  or

  n<> u<3> t<PortDir_Inp> p<7> s<6> l<1>
  n<> u<4> t<NetType_Wire> p<6> s<5> l<1>
  n<> u<5> t<Data_type_or_implicit> p<6> l<1>
  n<> u<6> t<Net_port_type> p<7> c<4> l<1>
  n<> u<7> t<Net_port_header> p<9> c<3> s<8> l<1>
  */

  NodeId net_port_header = fC->Child(id);
  NodeId identifier = fC->Sibling(net_port_header);
  NodeId net_port_type = fC->Child(net_port_header);
  VObjectType dir_type = fC->Type(net_port_type);
  if (dir_type == VObjectType::paPortDir_Out ||
      dir_type == VObjectType::paPortDir_Inp ||
      dir_type == VObjectType::paPortDir_Inout ||
      dir_type == VObjectType::paPortDir_Ref) {
    port_direction = dir_type;
    net_port_type = fC->Sibling(net_port_type);
    NodeId NetType = fC->Child(net_port_type);
    if (fC->Type(NetType) == VObjectType::paData_type_or_implicit) {
      NodeId Data_type = fC->Child(NetType);
      if (fC->Type(Data_type) == VObjectType::paData_type) {
        NetType = fC->Child(Data_type);
      }
    }

    NodeId packedDimension = fC->Sibling(NetType);
    if (fC->Type(packedDimension) ==
        VObjectType::slStringConst) {  // net type is class_scope
      packedDimension = fC->Sibling(packedDimension);
    }
    if (fC->Type(NetType) == VObjectType::paImplicit_data_type) {
      packedDimension = fC->Child(NetType);
      if (fC->Type(packedDimension) != VObjectType::paPacked_dimension) {
        packedDimension = InvalidNodeId;
      }
    }
    NodeId specParamId;
    bool is_signed = false;
    bool is_var = false;
    if (!packedDimension) {
      packedDimension = fC->Child(NetType);
    }

    if (fC->Type(packedDimension) == VObjectType::paSigning_Signed) {
      packedDimension = fC->Sibling(packedDimension);
    } else if (fC->Type(packedDimension) == VObjectType::paSigning_Unsigned) {
      packedDimension = fC->Sibling(packedDimension);
    }
    if (fC->Type(NetType) == VObjectType::paClass_scope) {
      specParamId = fC->Parent(NetType);
    } else if (fC->Type(NetType) == VObjectType::slStringConst) {
      specParamId = NetType;
    }
    if (fC->Type(packedDimension) != VObjectType::paPacked_dimension) {
      packedDimension = InvalidNodeId;
    }

    NodeId nodeType;
    VObjectType signal_type =
        getSignalType(fC, net_port_type, /*ref*/ packedDimension,
                      /*ref*/ is_signed, /*ref*/ is_var, /*ref*/ nodeType);
    NodeId unpackedDimension;
    NodeId defaultValue;
    NodeId tmp = fC->Sibling(identifier);
    if (fC->Type(tmp) == VObjectType::paUnpacked_dimension) {
      unpackedDimension = tmp;
    }
    if (fC->Type(tmp) == VObjectType::paConstant_expression) {
      defaultValue = tmp;
      if (dir_type == VObjectType::paPortDir_Ref) {
        Location loc(fC->getFileId(tmp), fC->Line(tmp), fC->Column(tmp),
                     m_session->getSymbolTable()->registerSymbol(
                         fC->SymName(identifier)));
        m_session->getErrorContainer()->addError(
            ErrorDefinition::COMP_ILLEGAL_DEFAULT_PORT_VALUE, loc, loc);
      }
    }
    if (!nodeType) {
      nodeType = NetType;
    }
    Signal* p =
        new Signal(component, fC, id, identifier, signal_type, port_direction,
                   packedDimension, unpackedDimension, is_signed);
    p->setTypespecId(specParamId ? specParamId : nodeType);
    p->uhdmScopeModel(compileDesign->getSerializer().topScope());
    if (is_var) p->setVar();
    p->setDefaultValue(defaultValue);
    p->setStatic();
    component->addPort(p);
    Signal* s =
        new Signal(component, fC, id, identifier, signal_type, port_direction,
                   packedDimension, unpackedDimension, is_signed);
    s->setTypespecId(specParamId ? specParamId : nodeType);
    s->uhdmScopeModel(compileDesign->getSerializer().topScope());
    if (is_var) s->setVar();
    s->setStatic();
    component->addSignal(s);
  } else if (fC->Type(net_port_header) ==
             VObjectType::paInterface_port_header) {
    NodeId interface_port_header = net_port_header;
    NodeId interface_identifier = fC->Child(interface_port_header);
    NodeId interface_name = fC->Child(interface_identifier);
    NodeId port_name = fC->Sibling(interface_port_header);
    NodeId unpacked_dimension = fC->Sibling(port_name);
    /*
    n<mem_if> u<10> t<StringConst> p<12> s<11> l<11>
    n<system> u<11> t<StringConst> p<12> l<11>
    n<> u<12> t<Interface_identifier> p<13> c<10> l<11>
    n<> u<13> t<Interface_port_header> p<15> c<12> s<14> l<11>
    n<sif2> u<14> t<StringConst> p<15> l<11>
    n<> u<15> t<Ansi_port_declaration> p<16> c<13> l<11>
    */
    Signal* s =
        new Signal(component, fC, net_port_header, port_name, interface_name,
                   VObjectType::slNoType, unpacked_dimension, false);
    s->uhdmScopeModel(compileDesign->getSerializer().topScope());
    s->setStatic();
    s->setTypespecId(interface_name);
    component->addPort(s);
  } else {
    NodeId data_type_or_implicit = fC->Child(net_port_type);
    NodeId data_type = fC->Child(data_type_or_implicit);
    if (data_type) {
      NodeId if_type_name_s = fC->Child(data_type);
      NodeId unpackedDimension = fC->Sibling(identifier);
      if (fC->Type(unpackedDimension) != VObjectType::paUnpacked_dimension)
        unpackedDimension = InvalidNodeId;
      if (fC->Type(if_type_name_s) == VObjectType::paIntVec_TypeReg ||
          fC->Type(if_type_name_s) == VObjectType::paIntVec_TypeLogic) {
        Signal* s = new Signal(component, fC, id, identifier,
                               fC->Type(if_type_name_s), VObjectType::slNoType,
                               InvalidNodeId, unpackedDimension, false);
        s->uhdmScopeModel(compileDesign->getSerializer().topScope());
        s->setStatic();
        s->setTypespecId(if_type_name_s);
        component->addPort(s);
        // DO NOT create signals for interfaces:
        // component->getSignals().emplace_back(s);
      } else {
        Signal* s = new Signal(component, fC, id, identifier, if_type_name_s,
                               VObjectType::slNoType, unpackedDimension, false);
        s->uhdmScopeModel(compileDesign->getSerializer().topScope());
        s->setStatic();
        s->setTypespecId(if_type_name_s);
        component->addPort(s);
        // DO NOT create signals for interfaces:
        // component->getSignals().emplace_back(s);
      }
    } else {
      VObjectType dataType = VObjectType::paData_type_or_implicit;
      NodeId packed;
      NodeId unpacked;
      bool is_signed = false;
      NodeId specParamId;
      // Reuse last signal data type (if any)
      Signal* last = nullptr;
      if (!component->getPorts().empty()) {
        last = component->getPorts().back();
        dataType = last->getType();
        packed = last->getPackedDimension();
        is_signed = last->isSigned();
        specParamId = last->getTypespecId();
        unpacked = last->getUnpackedDimension();
      }
      if (specParamId) {
        Signal* signal =
            new Signal(component, fC, id, identifier, dataType, port_direction,
                       packed, unpacked, is_signed);
        signal->uhdmScopeModel(compileDesign->getSerializer().topScope());
        signal->setTypespecId(specParamId);
        signal->setStatic();
        component->addPort(signal);
        component->addSignal(signal);
      } else {
        if (fC->Type(net_port_header) == VObjectType::paInterface_port_header) {
          dataType = VObjectType::paInterface_port_header;
        }
        Signal* signal =
            new Signal(component, fC, id, identifier, dataType, port_direction,
                       packed, InvalidNodeId, is_signed);
        signal->uhdmScopeModel(compileDesign->getSerializer().topScope());
        signal->setTypespecId(net_port_header);
        signal->setStatic();
        component->addPort(signal);
        component->addSignal(signal);
      }
    }
  }
  return true;
}

bool CompileHelper::compileNetDeclaration(
    DesignComponent* component, const FileContent* fC, NodeId id,
    bool interface, CompileDesign* compileDesign,
    uhdm::AttributeCollection* attributes) {
  /*
 n<> u<17> t<NetType_Wire> p<18> l<27>
 n<> u<18> t<NetTypeOrTrireg_Net> p<22> c<17> s<21> l<27>
 n<a> u<19> t<StringConst> p<20> l<27>
 n<> u<20> t<Net_decl_assignment> p<21> c<19> l<27>
 n<> u<21> t<List_of_net_decl_assignments> p<22> c<20> l<27>
 n<> u<22> t<Net_declaration> p<23> c<18> l<27>
   */
  NodeId List_of_net_decl_assignments;
  NodeId Packed_dimension;
  bool isSigned = false;
  VObjectType nettype = VObjectType::slNoType;
  VObjectType subnettype = VObjectType::slNoType;
  NodeId NetTypeOrTrireg_Net = fC->Child(id);
  NodeId NetType = fC->Child(NetTypeOrTrireg_Net);
  if (!NetType) {
    NetType = NetTypeOrTrireg_Net;
    nettype = fC->Type(NetType);
    if (NetType) {
      if (fC->SymName(NetType) == "logic") {
        nettype = VObjectType::paIntVec_TypeLogic;
      }
    }
    NodeId Data_type_or_implicit = fC->Sibling(NetType);
    NodeId Sign_or_Packed_dimension = fC->Child(Data_type_or_implicit);
    if (fC->Type(Sign_or_Packed_dimension) == VObjectType::paSigning_Signed) {
      isSigned = true;
      Sign_or_Packed_dimension = fC->Sibling(Sign_or_Packed_dimension);
    }
    if (fC->Type(Sign_or_Packed_dimension) == VObjectType::paPacked_dimension) {
      Packed_dimension = Sign_or_Packed_dimension;
    }
    if (fC->Type(Data_type_or_implicit) == VObjectType::paData_type_or_implicit)
      List_of_net_decl_assignments = fC->Sibling(Data_type_or_implicit);
    else
      List_of_net_decl_assignments = Data_type_or_implicit;
  } else {
    nettype = fC->Type(NetType);
    NodeId net = fC->Sibling(NetTypeOrTrireg_Net);
    if (fC->Type(net) == VObjectType::paPacked_dimension) {
      List_of_net_decl_assignments = fC->Sibling(net);
    } else {
      List_of_net_decl_assignments = net;
    }
  }

  NodeId delay;
  if (fC->Type(List_of_net_decl_assignments) == VObjectType::paDelay3 ||
      fC->Type(List_of_net_decl_assignments) == VObjectType::paDelay_control) {
    delay = List_of_net_decl_assignments;
    List_of_net_decl_assignments = fC->Sibling(List_of_net_decl_assignments);
  }
  NodeId net_decl_assignment = fC->Child(List_of_net_decl_assignments);
  if (!net_decl_assignment) {
    net_decl_assignment = List_of_net_decl_assignments;
  }
  while (net_decl_assignment) {
    NodeId signal = fC->Child(net_decl_assignment);
    if (!signal) {
      signal = net_decl_assignment;
    }
    Signal* portRef = nullptr;
    for (auto& port : component->getPorts()) {
      if (port->getName() == fC->SymName(signal)) {
        port->setType(fC->Type(NetType));
        portRef = port;
        break;
      }
    }
    NodeId Unpacked_dimension;
    NodeId tmp = fC->Sibling(signal);
    if (fC->Type(tmp) == VObjectType::paUnpacked_dimension) {
      Unpacked_dimension = tmp;
    }

    if (fC->Type(Packed_dimension) == VObjectType::paData_type) {
      NetType = fC->Child(Packed_dimension);
      if (fC->Type(NetType) !=
          VObjectType::paIntVec_TypeLogic) {  //"wire logic" is "wire"
        subnettype = nettype;
        nettype = fC->Type(NetType);
      }
    }

    if (nettype == VObjectType::slStringConst) {
      Signal* sig =
          new Signal(component, fC, net_decl_assignment, signal, InvalidNodeId,
                     subnettype, Unpacked_dimension, false);
      sig->uhdmScopeModel(compileDesign->getSerializer().topScope());
      if (portRef) portRef->setLowConn(sig);
      sig->setDelay(delay);
      sig->setStatic();
      sig->setTypespecId(NetType);
      if (isSigned) sig->setSigned();
      component->addSignal(sig);
    } else {
      Signal* sig = new Signal(component, fC, net_decl_assignment, signal,
                               nettype, VObjectType::slNoType, Packed_dimension,
                               Unpacked_dimension, false);
      sig->uhdmScopeModel(compileDesign->getSerializer().topScope());
      sig->setTypespecId(NetType);
      if (portRef) portRef->setLowConn(sig);
      sig->setDelay(delay);
      sig->setStatic();
      sig->attributes(attributes);
      if (isSigned) sig->setSigned();
      component->addSignal(sig);
    }

    net_decl_assignment = fC->Sibling(net_decl_assignment);
  }
  return true;
}

void CompileHelper::compileImportDeclaration(DesignComponent* component,
                                             const FileContent* fC,
                                             NodeId package_import_item_id,
                                             CompileDesign* compileDesign) {
  /*
     Verilog:
       import my_pkg::opcode_e, my_pkg::OPCODE_LOAD;
     Expected tree:
       n<my_pkg> u<27> t<StringConst> p<29> s<28> l<3>
       n<opcode_e> u<28> t<StringConst> p<29> l<3>
       n<> u<29> t<Package_import_item> p<33> c<27> s<32> l<3>
       n<my_pkg> u<30> t<StringConst> p<32> s<31> l<3>
       n<OPCODE_LOAD> u<31> t<StringConst> p<32> l<3>
       n<> u<32> t<Package_import_item> p<33> c<30> l<3>
       n<> u<33> t<Package_import_declaration> p<34> c<29> l<3>
     */
  uhdm::Any* pscope = component->getUhdmModel();
  if (pscope == nullptr)
    pscope = compileDesign->getCompiler()->getDesign()->getUhdmDesign();
  uhdm::Serializer& s = compileDesign->getSerializer();
  while (package_import_item_id) {
    uhdm::ImportTypespec* import_stmt = s.make<uhdm::ImportTypespec>();
    import_stmt->setParent(pscope);
    fC->populateCoreMembers(package_import_item_id, package_import_item_id,
                            import_stmt);
    import_stmt->setName(fC->SymName(package_import_item_id));
    NodeId package_name_id = fC->Child(package_import_item_id);

    NodeId item_name_id = fC->Sibling(package_name_id);
    Value* item_name = m_exprBuilder.getValueFactory().newStValue();
    if (item_name_id) {
      item_name->set(fC->SymName(item_name_id));
    } else {
      item_name->set("*");
    }
    if (uhdm::Constant* imported_item =
            constantFromValue(item_name, compileDesign)) {
      imported_item->setParent(import_stmt);
      if (item_name_id) {
        // In case of "*" item_name_id will be 0
        fC->populateCoreMembers(item_name_id, item_name_id, imported_item);
      } else {
        fC->populateCoreMembers(package_import_item_id, package_import_item_id,
                                imported_item);
      }
      import_stmt->setItem(imported_item);
    }
    m_exprBuilder.deleteValue(item_name);

    const std::string_view package_name = fC->SymName(package_name_id);
    import_stmt->setName(package_name);

    package_import_item_id = fC->Sibling(package_import_item_id);
    component->addImportTypespec(import_stmt);
  }
}

bool CompileHelper::compileDataDeclaration(
    DesignComponent* component, const FileContent* fC, NodeId id,
    bool interface, CompileDesign* compileDesign, Reduce reduce,
    uhdm::AttributeCollection* attributes) {
  NodeId subNode = fC->Child(id);
  VObjectType subType = fC->Type(subNode);
  switch (subType) {
    case VObjectType::paPackage_import_declaration:
      break;
    case VObjectType::paType_declaration:
    case VObjectType::paNet_type_declaration: {
      /*
        n<> u<15> t<Data_type> p<17> c<8> s<16> l<13>
        n<fsm_t> u<16> t<StringConst> p<17> l<13>
        n<> u<17> t<Type_declaration> p<18> c<15> l<13>
        n<> u<18> t<Data_declaration> p<19> c<17> l<13>
       */
      compileTypeDef(component, fC, id, compileDesign, reduce, nullptr);
      break;
    }
    default:
      /*
       n<> u<29> t<IntVec_TypeReg> p<30> l<29>
       n<> u<30> t<Data_type> p<34> c<29> s<33> l<29>
       n<b> u<31> t<StringConst> p<32> l<29>
       n<> u<32> t<Variable_decl_assignment> p<33> c<31> l<29>
       n<> u<33> t<List_of_variable_decl_assignments> p<34> c<32> l<29>
       n<> u<34> t<Variable_declaration> p<35> c<30> l<29>
       n<> u<35> t<Data_declaration> p<36> c<34> l<29>
       */
      NodeId data_decl = id;
      NodeId var_decl = fC->Child(data_decl);
      VObjectType type = fC->Type(data_decl);
      bool is_static = (valuedcomponenti_cast<ModuleDefinition*>(component) ||
                        valuedcomponenti_cast<Program>(component));
      if (fC->Type(var_decl) == VObjectType::paLifetime_Automatic) {
        is_static = false;
        data_decl = fC->Sibling(var_decl);
        var_decl = data_decl;
      } else if (type == VObjectType::paData_declaration) {
        data_decl = fC->Child(data_decl);
        type = fC->Type(data_decl);
        var_decl = data_decl;
      }
      bool is_local = false;
      bool is_protected = false;
      bool is_rand = false;
      bool is_randc = false;
      bool is_const = false;
      bool is_signed = false;
      while ((type == VObjectType::paPropQualifier_ClassItem) ||
             (type == VObjectType::paPropQualifier_Rand) ||
             (type == VObjectType::paPropQualifier_Randc) ||
             (type == VObjectType::paConst_type) ||
             (type == VObjectType::paLifetime_Static)) {
        NodeId qualifier = fC->Child(data_decl);
        VObjectType qualType = fC->Type(qualifier);
        if (qualType == VObjectType::paClassItemQualifier_Protected)
          is_protected = true;
        if (qualType == VObjectType::paClassItemQualifier_Static)
          is_static = true;
        if (qualType == VObjectType::paClassItemQualifier_Local)
          is_local = true;
        if (type == VObjectType::paPropQualifier_Rand) is_rand = true;
        if (type == VObjectType::paPropQualifier_Randc) is_randc = true;
        if (type == VObjectType::paConst_type) is_const = true;
        if (type == VObjectType::paLifetime_Static) is_static = true;
        data_decl = fC->Sibling(data_decl);
        type = fC->Type(data_decl);
        var_decl = data_decl;
      }

      NodeId variable_declaration = var_decl;
      if (fC->Type(variable_declaration) == VObjectType::paData_declaration)
        variable_declaration = fC->Child(variable_declaration);
      bool var_type = false;
      if (fC->Type(variable_declaration) == VObjectType::paConst_type) {
        variable_declaration = fC->Sibling(variable_declaration);
        is_const = true;
      }
      if (fC->Type(variable_declaration) == VObjectType::paVar_type) {
        variable_declaration = fC->Sibling(variable_declaration);
        var_type = true;
      }
      NodeId data_type = fC->Child(variable_declaration);
      NodeId intVec_TypeReg = fC->Child(data_type);
      if (fC->Type(intVec_TypeReg) == VObjectType::paVIRTUAL)
        intVec_TypeReg = fC->Sibling(intVec_TypeReg);
      if (fC->Type(intVec_TypeReg) == VObjectType::paIntegerAtomType_Byte ||
          fC->Type(intVec_TypeReg) == VObjectType::paIntegerAtomType_Int ||
          fC->Type(intVec_TypeReg) == VObjectType::paIntegerAtomType_Integer ||
          fC->Type(intVec_TypeReg) == VObjectType::paIntegerAtomType_LongInt ||
          fC->Type(intVec_TypeReg) == VObjectType::paIntegerAtomType_Shortint ||
          fC->Type(intVec_TypeReg) == VObjectType::paReal_number) {
        is_signed = true;
      }
      NodeId packedDimension = fC->Sibling(intVec_TypeReg);
      if (fC->Type(packedDimension) == VObjectType::slStringConst) {
        // class or package name;
        if (fC->Type(fC->Sibling(packedDimension)) ==
            VObjectType::paPacked_dimension) {
          packedDimension = fC->Sibling(packedDimension);
        } else {
          packedDimension = InvalidNodeId;
        }
      } else if (fC->Type(packedDimension) == VObjectType::paSigning_Signed) {
        is_signed = true;
        packedDimension = fC->Sibling(packedDimension);
      } else if (fC->Type(packedDimension) == VObjectType::paSigning_Unsigned) {
        packedDimension = fC->Sibling(packedDimension);
        is_signed = false;
      }
      NodeId unpackedDimension;
      NodeId list_of_variable_decl_assignments = fC->Sibling(data_type);
      if (fC->Type(list_of_variable_decl_assignments) ==
          VObjectType::paPacked_dimension) {
        list_of_variable_decl_assignments =
            fC->Sibling(list_of_variable_decl_assignments);
      }
      NodeId variable_decl_assignment =
          fC->Child(list_of_variable_decl_assignments);
      while (variable_decl_assignment) {
        NodeId signal = fC->Child(variable_decl_assignment);
        Signal* portRef = nullptr;
        unpackedDimension = fC->Sibling(signal);
        for (Signal* port : component->getPorts()) {
          if (port->getName() == fC->SymName(signal)) {
            port->setType(fC->Type(intVec_TypeReg));
            portRef = port;
            break;
          }
        }

        VObjectType sigType = fC->Type(intVec_TypeReg);
        Signal* sig = new Signal(component, fC, var_decl, signal, sigType,
                                 VObjectType::slNoType, packedDimension,
                                 unpackedDimension, false);
        if (sigType == VObjectType::paInterface_identifier) {
          sig->setInterfaceTypespecId(data_type);
        } else {
          sig->setTypespecId(data_type);
        }
        sig->uhdmScopeModel(compileDesign->getSerializer().topScope());
        if (is_const) sig->setConst();
        if (var_type) sig->setVar();
        if (portRef) portRef->setLowConn(sig);
        if (is_local) sig->setLocal();
        if (is_static) sig->setStatic();
        if (is_protected) sig->setProtected();
        if (is_rand) sig->setRand();
        if (is_randc) sig->setRandc();
        if (is_signed) sig->setSigned();
        sig->attributes(attributes);
        component->addSignal(sig);
        variable_decl_assignment = fC->Sibling(variable_decl_assignment);
      }
      break;
  }
  return true;
}

uhdm::ContAssignCollection CompileHelper::compileContinuousAssignment(
    DesignComponent* component, const FileContent* fC, NodeId id,
    CompileDesign* compileDesign, uhdm::Any* pstmt,
    ValuedComponentI* instance) {
  uhdm::Serializer& s = compileDesign->getSerializer();
  uhdm::ContAssignCollection assigns;
  NodeId List_of_net_assignments = id;
  /*
    n<o> u<6> t<StringConst> p<7> l<4>
    n<> u<7> t<Ps_or_hierarchical_identifier> p<10> c<6> s<9> l<4>
    n<> u<8> t<Constant_bit_select> p<9> l<4>
    n<> u<9> t<Constant_select> p<10> c<8> l<4>
    n<> u<10> t<Net_lvalue> p<15> c<7> s<14> l<4>
    n<i> u<11> t<StringConst> p<12> l<4>
    n<> u<12> t<Primary_literal> p<13> c<11> l<4>
    n<> u<13> t<Primary> p<14> c<12> l<4>
    n<> u<14> t<Expression> p<15> c<13> l<4>
    n<> u<15> t<Net_assignment> p<16> c<10> l<4>
    n<> u<16> t<List_of_net_assignments> p<17> c<15> l<4>
    n<> u<17> t<Continuous_assign> p<18> c<16> l<4>
  */
  NodeId Strength0;
  NodeId Strength1;
  NodeId delayExprId;

  if (fC->Type(List_of_net_assignments) == VObjectType::paDrive_strength) {
    NodeId Drive_strength = List_of_net_assignments;
    Strength0 = fC->Child(Drive_strength);
    Strength1 = fC->Sibling(Strength0);
    List_of_net_assignments = fC->Sibling(List_of_net_assignments);
  } else if (fC->Type(List_of_net_assignments) == VObjectType::paDelay3) {
    delayExprId = List_of_net_assignments;
    List_of_net_assignments = fC->Sibling(List_of_net_assignments);
  }

  NodeId Net_assignment = fC->Child(List_of_net_assignments);
  while (Net_assignment) {
    NodeId Net_lvalue = fC->Child(Net_assignment);
    NodeId Expression = fC->Sibling(Net_lvalue);
    if (Expression &&
        (fC->Type(Expression) != VObjectType::paUnpacked_dimension)) {
      uhdm::ContAssign* cassign = s.make<uhdm::ContAssign>();
      cassign->setParent(pstmt);

      // Delay Expr
      if (delayExprId) {
        if (uhdm::Expr* delay_expr = (uhdm::Expr*)compileExpression(
                component, fC, delayExprId, compileDesign, Reduce::No, cassign,
                instance)) {
          cassign->setDelay(delay_expr);
        }
      }

      // LHS
      NodeId Ps_or_hierarchical_identifier = fC->Child(Net_lvalue);
      NodeId Hierarchical_identifier = Ps_or_hierarchical_identifier;
      if (fC->Type(fC->Child(Ps_or_hierarchical_identifier)) ==
          VObjectType::paHierarchical_identifier) {
        Hierarchical_identifier = fC->Child(fC->Child(Hierarchical_identifier));
      }

      if (uhdm ::Any* lhs_exp =
              compileExpression(component, fC, Hierarchical_identifier,
                                compileDesign, Reduce::No, cassign, instance)) {
        NodeId Constant_select = fC->Sibling(Ps_or_hierarchical_identifier);
        if ((fC->Type(Constant_select) == VObjectType::paConstant_select) &&
            (Ps_or_hierarchical_identifier != Hierarchical_identifier) &&
            (lhs_exp->getUhdmType() == uhdm::UhdmType::HierPath)) {
          NodeId identifierId = fC->Sibling(Hierarchical_identifier);
          while (identifierId &&
                 (fC->Type(identifierId) != VObjectType::slStringConst))
            identifierId = fC->Sibling(identifierId);
          std::string_view identifierName;
          if (fC->Type(identifierId) == VObjectType::slStringConst)
            identifierName = fC->SymName(identifierId);
          if (uhdm::Any* sel = compileSelectExpression(
                  component, fC, fC->Child(Constant_select), identifierName,
                  compileDesign, Reduce::No, lhs_exp, instance, false)) {
            uhdm::HierPath* path = (uhdm::HierPath*)lhs_exp;
            uhdm::Any* last = path->getPathElems()->back();
            if (last->getUhdmType() == uhdm::UhdmType::RefObj &&
                sel->getUhdmType() == uhdm::UhdmType::BitSelect) {
              uhdm::RefObj* last_ro = (uhdm::RefObj*)last;
              uhdm::BitSelect* sel_bs = (uhdm::BitSelect*)sel;
              path->getPathElems()->pop_back();
              sel_bs->setName(last->getName());
              sel_bs->setStartLine(last->getStartLine());
              sel_bs->setStartColumn(last->getStartColumn());
              sel_bs->setFullName(
                  StrCat(last_ro->getFullName(), decompileHelper(sel)));
            }
            path->getPathElems()->emplace_back(sel);
            std::string path_name(path->getName());
            path_name += decompileHelper(sel);
            path->setName(path_name);
            path->setFullName(path_name);
          }
        }
        cassign->setLhs((uhdm::Expr*)lhs_exp);
        lhs_exp->setParent(cassign);
      }

      // RHS
      if (uhdm::Any* rhs_exp =
              compileExpression(component, fC, Expression, compileDesign,
                                Reduce::No, cassign, instance)) {
        cassign->setRhs((uhdm::Expr*)rhs_exp);
        rhs_exp->setParent(cassign);
      }

      if (Strength0) {
        VObjectType st0 = fC->Type(Strength0);
        if (st0 == VObjectType::paSUPPLY0 || st0 == VObjectType::paSTRONG0 ||
            st0 == VObjectType::paPULL0 || st0 == VObjectType::paWEAK0 ||
            st0 == VObjectType::paHIGHZ0) {
          cassign->setStrength0(
              UhdmWriter::getStrengthType(fC->Type(Strength0)));
        } else {
          cassign->setStrength1(
              UhdmWriter::getStrengthType(fC->Type(Strength0)));
        }
      }

      if (Strength1) {
        VObjectType st1 = fC->Type(Strength1);
        if (st1 == VObjectType::paSUPPLY0 || st1 == VObjectType::paSTRONG0 ||
            st1 == VObjectType::paPULL0 || st1 == VObjectType::paWEAK0 ||
            st1 == VObjectType::paHIGHZ0) {
          cassign->setStrength0(
              UhdmWriter::getStrengthType(fC->Type(Strength1)));
        } else {
          cassign->setStrength1(
              UhdmWriter::getStrengthType(fC->Type(Strength1)));
        }
      }

      fC->populateCoreMembers(id, List_of_net_assignments, cassign);
      assigns.emplace_back(cassign);
    }
    Net_assignment = fC->Sibling(Net_assignment);
  }
  return assigns;
}

std::string CompileHelper::decompileHelper(const uhdm::Any* sel) {
  std::string path_name;
  uhdm::ExprEval eval;
  if (sel == nullptr) {
    return "";
  }
  if (sel->getUhdmType() == uhdm::UhdmType::Constant) {
    const std::string_view ind = ((uhdm::Expr*)sel)->getDecompile();
    path_name.append(ind);
  } else if (sel->getUhdmType() == uhdm::UhdmType::RefObj) {
    const std::string_view ind = ((uhdm::Expr*)sel)->getName();
    path_name.append(ind);
  } else if (sel->getUhdmType() == uhdm::UhdmType::Operation) {
    path_name.append(eval.prettyPrint(sel));
  } else if (sel->getUhdmType() == uhdm::UhdmType::BitSelect) {
    uhdm::BitSelect* bsel = (uhdm::BitSelect*)sel;
    const uhdm::Expr* index = bsel->getIndex();
    if (index->getUhdmType() == uhdm::UhdmType::Constant) {
      const std::string_view ind = ((uhdm::Expr*)index)->getDecompile();
      path_name.append("[").append(ind).append("]");
    } else if (index->getUhdmType() == uhdm::UhdmType::RefObj) {
      const std::string_view ind = ((uhdm::Expr*)index)->getName();
      path_name.append("[").append(ind).append("]");
    } else if (index->getUhdmType() == uhdm::UhdmType::Operation) {
      path_name.append("[" + eval.prettyPrint(index) + "]");
    }
  } else if (const uhdm::PartSelect* pselect =
                 any_cast<const uhdm::PartSelect*>(sel)) {
    std::string selectRange =
        StrCat("[", decompileHelper(pselect->getLeftExpr()), ":",
               decompileHelper(pselect->getRightExpr()), "]");
    path_name += selectRange;
  } else if (const uhdm::IndexedPartSelect* pselect =
                 any_cast<const uhdm::IndexedPartSelect*>(sel)) {
    std::string selectRange = StrCat(
        "[", decompileHelper(pselect->getBaseExpr()),
        ((pselect->getIndexedPartSelectType() == vpiPosIndexed) ? "+" : "-"),
        ":", decompileHelper(pselect->getWidthExpr()), "]");
    path_name += selectRange;
  } else if (const uhdm::VarSelect* pselect =
                 any_cast<const uhdm::VarSelect*>(sel)) {
    std::string selectRange;
    uhdm::ExprCollection* exprs = pselect->getIndexes();
    for (auto ex : *exprs) {
      std::string tmp = decompileHelper(ex);
      if ((!tmp.empty()) && tmp[0] != '[') selectRange += StrCat("[");
      selectRange += StrCat(tmp);
      if ((!tmp.empty()) && tmp[0] != '[') selectRange += StrCat("]");
    }
    path_name += selectRange;
  }
  return path_name;
}

std::pair<std::vector<uhdm::ModuleArray*>, std::vector<uhdm::RefModule*>>
CompileHelper::compileInstantiation(ModuleDefinition* mod,
                                    const FileContent* fC,
                                    CompileDesign* compileDesign,
                                    uhdm::Any* pexpr, NodeId id,
                                    ValuedComponentI* instance) {
  std::pair<std::vector<uhdm::ModuleArray*>, std::vector<uhdm::RefModule*>>
      results;
  uhdm::Serializer& s = compileDesign->getSerializer();
  Design* const design = compileDesign->getCompiler()->getDesign();
  NodeId moduleName = fC->sl_collect(id, VObjectType::slStringConst);
  const std::string_view libName = fC->getLibrary()->getName();
  const std::string_view mname = fC->SymName(moduleName);
  std::string modName = StrCat(libName, "@", mname);
  ModuleDefinition* parentModuleDefinition =
      design->getModuleDefinition(modName);
  if (parentModuleDefinition == nullptr) parentModuleDefinition = mod;

  uhdm::Scope* parentScope = any_cast<uhdm::Scope>(pexpr);
  if (parentScope == nullptr) parentScope = mod->getUhdmModel<uhdm::Module>();

  uhdm::ModuleTypespec* tps = nullptr;
  NodeId typespecId = fC->Child(id);
  const std::string_view typespecName = fC->SymName(typespecId);
  if (uhdm::TypespecCollection* const typespecs = parentScope->getTypespecs()) {
    for (uhdm::Typespec* t : *typespecs) {
      if (uhdm::ModuleTypespec* const mt = any_cast<uhdm::ModuleTypespec>(t)) {
        if (mt->getName() == typespecName) {
          tps = mt;
          break;
        }
      }
    }
  }

  if (tps == nullptr) {
    tps = s.make<uhdm::ModuleTypespec>();
    tps->setName(typespecName);
    tps->setParent(parentScope);
    fC->populateCoreMembers(typespecId, typespecId, tps);
  }

  NodeId hierInstId = fC->sl_collect(id, VObjectType::paHierarchical_instance);
  if (!hierInstId) hierInstId = fC->sl_collect(id, VObjectType::paUdp_instance);
  while (hierInstId) {
    NodeId instId = fC->sl_collect(hierInstId, VObjectType::paName_of_instance);
    NodeId identifierId = fC->Child(instId);
    std::string_view instName = fC->SymName(identifierId);

    if (NodeId unpackedDimId = fC->Sibling(identifierId)) {
      int32_t unpackedSize = 0;
      if (std::vector<uhdm::Range*>* unpackedDimensions =
              compileRanges(mod, fC, unpackedDimId, compileDesign, Reduce::No,
                            nullptr, instance, unpackedSize, false)) {
        uhdm::ModuleArray* mod_array = s.make<uhdm::ModuleArray>();
        mod_array->setRanges(unpackedDimensions);
        mod_array->setName(instName);
        mod_array->setFullName(modName);
        for (auto r : *unpackedDimensions) r->setParent(mod_array);

        uhdm::RefTypespec* tpsRef = s.make<uhdm::RefTypespec>();
        tpsRef->setName(fC->SymName(typespecId));
        tpsRef->setParent(mod_array);
        fC->populateCoreMembers(typespecId, typespecId, tpsRef);
        mod_array->setElemTypespec(tpsRef);
        mod_array->getElemTypespec()->setActual(tps);

        compileHighConn(parentModuleDefinition, fC, compileDesign, id,
                        mod_array->getPorts(true), mod_array);
        fC->populateCoreMembers(identifierId, identifierId, mod_array);
        results.first.emplace_back(mod_array);
      }
    } else {
      // Simple instance
      uhdm::RefModule* m = s.make<uhdm::RefModule>();
      m->setName(instName);
      m->setDefName(modName);
      m->setParent(parentScope);
      fC->populateCoreMembers(moduleName, moduleName, m);
      results.second.emplace_back(m);
      compileHighConn(parentModuleDefinition, fC, compileDesign, id,
                      m->getPorts(true), m);
    }
    hierInstId = fC->Sibling(hierInstId);
  }
  return results;
}

uint32_t CompileHelper::getBuiltinType(VObjectType type) {
  switch (type) {
    case VObjectType::paNInpGate_And:
      return vpiAndPrim;
    case VObjectType::paNInpGate_Or:
      return vpiOrPrim;
    case VObjectType::paNInpGate_Nor:
      return vpiNorPrim;
    case VObjectType::paNInpGate_Nand:
      return vpiNandPrim;
    case VObjectType::paNInpGate_Xor:
      return vpiXorPrim;
    case VObjectType::paNInpGate_Xnor:
      return vpiXnorPrim;
    case VObjectType::paNOutGate_Buf:
      return vpiBufPrim;
    case VObjectType::paNOutGate_Not:
      return vpiNotPrim;
    case VObjectType::paPassEnSwitch_Tranif0:
      return vpiTranif0Prim;
    case VObjectType::paPassEnSwitch_Tranif1:
      return vpiTranif1Prim;
    case VObjectType::paPassEnSwitch_RTranif1:
      return vpiRtranif1Prim;
    case VObjectType::paPassEnSwitch_RTranif0:
      return vpiRtranif0Prim;
    case VObjectType::paPassSwitch_Tran:
      return vpiTranPrim;
    case VObjectType::paPassSwitch_RTran:
      return vpiRtranPrim;
    case VObjectType::paCmosSwitchType_Cmos:
      return vpiCmosPrim;
    case VObjectType::paCmosSwitchType_RCmos:
      return vpiRcmosPrim;
    case VObjectType::paEnableGateType_Bufif0:
      return vpiBufif0Prim;
    case VObjectType::paEnableGateType_Bufif1:
      return vpiBufif1Prim;
    case VObjectType::paEnableGateType_Notif0:
      return vpiNotif0Prim;
    case VObjectType::paEnableGateType_Notif1:
      return vpiNotif1Prim;
    case VObjectType::paMosSwitchType_NMos:
      return vpiNmosPrim;
    case VObjectType::paMosSwitchType_PMos:
      return vpiPmosPrim;
    case VObjectType::paMosSwitchType_RNMos:
      return vpiRnmosPrim;
    case VObjectType::paMosSwitchType_RPMos:
      return vpiRpmosPrim;
    case VObjectType::paPULLUP:
      return vpiPullupPrim;
    case VObjectType::paPULLDOWN:
      return vpiPulldownPrim;
    default:
      return 0;
  }
}

void CompileHelper::compileUdpInstantiation(ModuleDefinition* mod,
                                            const FileContent* fC,
                                            CompileDesign* compileDesign,
                                            NodeId id,
                                            ValuedComponentI* instance) {
  VObjectTypeUnorderedSet insttypes = {VObjectType::paUdp_instance};
  uhdm::Serializer& s = compileDesign->getSerializer();
  std::vector<NodeId> hierInstIds = fC->sl_collect_all(id, insttypes, true);
  NodeId hierInstId;
  if (!hierInstIds.empty()) hierInstId = hierInstIds[0];
  NodeId udpDefId = fC->Child(id);
  if (!hierInstId) return;
  std::string_view instName;
  while (hierInstId) {
    NodeId instId = fC->sl_collect(hierInstId, VObjectType::paName_of_instance);
    NodeId identifierId;
    NodeId Net_lvalue;
    if (instId) {
      identifierId = fC->Child(instId);
      instName = fC->SymName(identifierId);
      Net_lvalue = fC->Sibling(instId);
    }

    NodeId unpackedDimId;
    if (identifierId) unpackedDimId = fC->Sibling(identifierId);
    uhdm::Udp* udp = s.make<uhdm::Udp>();
    uhdm::Primitive* gate = udp;
    if (unpackedDimId &&
        (fC->Type(unpackedDimId) == VObjectType::paUnpacked_dimension)) {
      // Vector instances
      int32_t size;
      uhdm::RangeCollection* ranges =
          compileRanges(mod, fC, unpackedDimId, compileDesign, Reduce::No,
                        nullptr, instance, size, false);
      if (mod->getPrimitiveArrays() == nullptr) {
        mod->setPrimitiveArrays(s.makeCollection<uhdm::PrimitiveArray>());
      }
      uhdm::PrimitiveArray* gate_array = s.make<uhdm::UdpArray>();
      gate_array->setRanges(ranges);
      gate_array->getPrimitives(true)->emplace_back(gate);
      mod->getPrimitiveArrays()->emplace_back(gate_array);
    } else {
      if (mod->getPrimitives() == nullptr) {
        mod->setPrimitives(s.makeCollection<uhdm::Primitive>());
      }
      mod->getPrimitives()->emplace_back(gate);
    }

    gate->setName(instName);
    gate->setDefName(fC->SymName(udpDefId));
    fC->populateCoreMembers(id, id, gate);
    writePrimTerms(mod, fC, compileDesign, Net_lvalue, gate, 0, instance);
    hierInstId = fC->Sibling(hierInstId);
  }
}

void CompileHelper::writePrimTerms(ModuleDefinition* mod, const FileContent* fC,
                                   CompileDesign* compileDesign, NodeId id,
                                   uhdm::Primitive* prim, int32_t vpiGateType,
                                   ValuedComponentI* instance) {
  uhdm::Serializer& s = compileDesign->getSerializer();
  uint32_t index = 0;
  while (id) {
    uhdm::PrimTerm* term = s.make<uhdm::PrimTerm>();
    fC->populateCoreMembers(id, id, term);
    term->setParent(prim);
    term->setTermIndex(index);
    prim->getPrimTerms(true)->emplace_back(term);

    NodeId expId = fC->Child(id);
    if (uhdm::Expr* hconn = (uhdm::Expr*)compileExpression(
            mod, fC, expId, compileDesign, Reduce::No, term, nullptr)) {
      term->setExpr(hconn);
    }

    if (vpiGateType == vpiBufPrim || vpiGateType == vpiNotPrim) {
      if (index == 0) {
        term->setDirection(vpiOutput);
      } else {
        term->setDirection(vpiInput);
      }
    } else if (vpiGateType == vpiTranif1Prim || vpiGateType == vpiTranif0Prim ||
               vpiGateType == vpiRtranif1Prim ||
               vpiGateType == vpiRtranif0Prim || vpiGateType == vpiTranPrim ||
               vpiGateType == vpiRtranPrim) {
      if (index == 0) {
        term->setDirection(vpiInout);
      } else {
        term->setDirection(vpiInput);
      }
    } else {
      if (index == 0) {
        term->setDirection(vpiOutput);
      } else {
        term->setDirection(vpiInput);
      }
    }
    index++;

    id = fC->Sibling(id);
  }
}

void CompileHelper::compileGateInstantiation(ModuleDefinition* mod,
                                             const FileContent* fC,
                                             CompileDesign* compileDesign,
                                             NodeId id,
                                             ValuedComponentI* instance) {
  uhdm::Serializer& s = compileDesign->getSerializer();
  uhdm::Primitive* gate = nullptr;
  uhdm::PrimitiveArray* gate_array = nullptr;
  NodeId gatenode = fC->Child(fC->Parent(id));
  VObjectType gatetype = fC->Type(gatenode);
  int32_t vpiGateType = getBuiltinType(gatetype);
  NodeId Name_of_instance = fC->Child(id);
  NodeId Name = fC->Child(Name_of_instance);
  NodeId Unpacked_dimension = fC->Sibling(Name);
  if (vpiGateType == vpiPmosPrim || vpiGateType == vpiRpmosPrim ||
      vpiGateType == vpiNmosPrim || vpiGateType == vpiRnmosPrim ||
      vpiGateType == vpiCmosPrim || vpiGateType == vpiRcmosPrim ||
      vpiGateType == vpiTranif1Prim || vpiGateType == vpiTranif0Prim ||
      vpiGateType == vpiRtranif1Prim || vpiGateType == vpiRtranif0Prim ||
      vpiGateType == vpiTranPrim || vpiGateType == vpiRtranPrim) {
    gate = s.make<uhdm::SwitchTran>();
    if (fC->Type(Unpacked_dimension) == VObjectType::paUnpacked_dimension) {
      gate_array = s.make<uhdm::SwitchArray>();
      int32_t size;
      uhdm::RangeCollection* ranges =
          compileRanges(mod, fC, Unpacked_dimension, compileDesign, Reduce::No,
                        nullptr, instance, size, false);
      gate_array->setRanges(ranges);
      gate_array->getPrimitives(true)->emplace_back(gate);
      if (mod->getPrimitiveArrays() == nullptr) {
        mod->setPrimitiveArrays(s.makeCollection<uhdm::PrimitiveArray>());
      }
      mod->getPrimitiveArrays()->emplace_back(gate_array);
    } else {
      if (mod->getPrimitives() == nullptr) {
        mod->setPrimitives(s.makeCollection<uhdm::Primitive>());
      }
      mod->getPrimitives()->emplace_back(gate);
    }
    gate->setPrimType(vpiGateType);
  } else {
    gate = s.make<uhdm::Gate>();
    if (fC->Type(Unpacked_dimension) == VObjectType::paUnpacked_dimension) {
      gate_array = s.make<uhdm::GateArray>();
      gate_array->setName(fC->SymName(Name));
      fC->populateCoreMembers(id, id, gate_array);
      int32_t size;
      if (uhdm::RangeCollection* ranges =
              compileRanges(mod, fC, Unpacked_dimension, compileDesign,
                            Reduce::No, gate_array, instance, size, false)) {
        gate_array->setRanges(ranges);
      }
      gate->setParent(gate_array);
      gate_array->getPrimitives(true)->emplace_back(gate);
      if (mod->getPrimitiveArrays() == nullptr) {
        mod->setPrimitiveArrays(s.makeCollection<uhdm::PrimitiveArray>());
      }
      mod->getPrimitiveArrays()->emplace_back(gate_array);
    } else {
      if (mod->getPrimitives() == nullptr) {
        mod->setPrimitives(s.makeCollection<uhdm::Primitive>());
      }
      mod->getPrimitives()->emplace_back(gate);
    }

    gate->setPrimType(vpiGateType);
  }
  if (gate) {
    gate->setName(fC->SymName(Name));
    gate->setDefName(UhdmWriter::builtinGateName(gatetype));
    fC->populateCoreMembers(id, id, gate);
  }
  NodeId Net_lvalue = fC->Sibling(Name_of_instance);
  writePrimTerms(mod, fC, compileDesign, Net_lvalue, gate, vpiGateType,
                 instance);
}

void CompileHelper::compileHighConn(ModuleDefinition* component,
                                    const FileContent* fC,
                                    CompileDesign* compileDesign, NodeId instId,
                                    uhdm::PortCollection* ports,
                                    uhdm::Any* pexpr) {
  FileSystem* const fileSystem = m_session->getFileSystem();
  NodeId Udp_instantiation = instId;
  uhdm::Serializer& s = compileDesign->getSerializer();
  VObjectType inst_type = fC->Type(Udp_instantiation);
  const std::vector<Signal*>& signals = component->getPorts();

  std::map<std::string_view, Signal*> allSignals;
  std::map<std::string_view, Signal*> allSignalsConst;

  for (Signal* s : signals) {
    allSignals.emplace(s->getName(), s);
    allSignalsConst.emplace(s->getName(), s);
  }

  if ((inst_type == VObjectType::paUdp_instantiation) ||
      (inst_type == VObjectType::paModule_instantiation) ||
      (inst_type == VObjectType::paProgram_instantiation) ||
      (inst_type == VObjectType::paInterface_instantiation) ||
      (inst_type == VObjectType::paCmos_switch_instance) ||
      (inst_type == VObjectType::paEnable_gate_instance) ||
      (inst_type == VObjectType::paMos_switch_instance) ||
      (inst_type == VObjectType::paN_input_gate_instance) ||
      (inst_type == VObjectType::paN_output_gate_instance) ||
      (inst_type == VObjectType::paPass_enable_switch_instance) ||
      (inst_type == VObjectType::paPass_switch_instance) ||
      (inst_type == VObjectType::paPull_gate_instance)) {
    /*
    n<DUT> u<178> t<StringConst> p<191> s<190> l<20>
    n<dut> u<179> t<StringConst> p<180> l<20>
    n<> u<180> t<Name_of_instance> p<190> c<179> s<185> l<20>
    n<i> u<181> t<StringConst> p<182> l<20>
    n<> u<182> t<Ps_or_hierarchical_identifier> p<185> c<181> s<184> l<20>
    n<> u<183> t<Constant_bit_select> p<184> l<20>
    n<> u<184> t<Constant_select> p<185> c<183> l<20>
    n<> u<185> t<Net_lvalue> p<190> c<182> s<189> l<20>
    n<o> u<186> t<StringConst> p<187> l<20>
    n<> u<187> t<Primary_literal> p<188> c<186> l<20>
    n<> u<188> t<Primary> p<189> c<187> l<20>
    n<> u<189> t<Expression> p<190> c<188> l<20>
    n<> u<190> t<Udp_instance> p<191> c<180> l<20>
    n<> u<191> t<Udp_instantiation> p<192> c<178> l<20>
    */
    NodeId modId = fC->Child(Udp_instantiation);
    NodeId Udp_instance = fC->Sibling(modId);
    if ((inst_type == VObjectType::paCmos_switch_instance) ||
        (inst_type == VObjectType::paEnable_gate_instance) ||
        (inst_type == VObjectType::paMos_switch_instance) ||
        (inst_type == VObjectType::paN_input_gate_instance) ||
        (inst_type == VObjectType::paN_output_gate_instance) ||
        (inst_type == VObjectType::paPass_enable_switch_instance) ||
        (inst_type == VObjectType::paPass_switch_instance) ||
        (inst_type == VObjectType::paPull_gate_instance)) {
      modId = fC->Child(fC->Parent(Udp_instantiation));
      Udp_instance = Udp_instantiation;
      // In the case of single instance, point to the delay or parameter
      NodeId tmp = fC->Sibling(modId);
      if ((fC->Type(tmp) == VObjectType::paParameter_value_assignment) ||
          (fC->Type(tmp) == VObjectType::paDelay2) ||
          (fC->Type(tmp) == VObjectType::paDelay3)) {
        Udp_instance = tmp;
      }
    }
    if (fC->Type(Udp_instance) == VObjectType::paParameter_value_assignment) {
      Udp_instance = fC->Sibling(Udp_instance);
    } else if (fC->Type(Udp_instance) == VObjectType::paDelay2 ||
               fC->Type(Udp_instance) == VObjectType::paDelay3) {
      checkForLoops(true);
      if (uhdm::Expr* delay_expr = (uhdm::Expr*)compileExpression(
              component, fC, Udp_instance, compileDesign, Reduce::Yes, nullptr,
              nullptr)) {
        // TODO(HS): Figure out how to use the delay here!
        // UhdmWriter sets the value on the gate if the array has only one
        // element.
        uhdm::ExprCollection* delays = s.makeCollection<uhdm::Expr>();
        delays->emplace_back(delay_expr);
      }
      checkForLoops(false);
      Udp_instance = fC->Sibling(Udp_instance);
    }
    NodeId Net_lvalue;
    if (const NodeId Name_of_instance = fC->Child(Udp_instance);
        fC->Type(Name_of_instance) == VObjectType::paName_of_instance) {
      Net_lvalue = fC->Sibling(Name_of_instance);
      //  // TODO(HS): Do something about this!
      //  // UhdmWriter::creates udp_array based on this range!
      //} else {
      //  Net_lvalue = Name_of_instance;
      //  NodeId Name = fC->Child(Name_of_instance);
      //  NodeId Unpacked_dimension = fC->Sibling(Name);
      //  if (Unpacked_dimension) {
      //    int32_t size;
      //    checkForLoops(true);
      //    if (uhdm::RangeCollection* ranges =
      //            compileRanges(component, fC, Unpacked_dimension,
      //            compileDesign,
      //                          Reduce::Yes, nullptr, nullptr, size, false)) {
      //      ranges = nullptr;
      //    }
      //    checkForLoops(false);
      //  }
    }
    if (fC->Type(Net_lvalue) == VObjectType::paNet_lvalue) {
      uint32_t index = 0;
      while (Net_lvalue) {
        std::string sigName;
        NodeId sigId;
        bool bit_or_part_select = false;
        if (fC->Type(Net_lvalue) == VObjectType::paNet_lvalue) {
          NodeId Hierarchical_identifier = fC->Child(Net_lvalue);
          if (fC->Type(fC->Child(Hierarchical_identifier)) ==
              VObjectType::paHierarchical_identifier) {
            Hierarchical_identifier =
                fC->Child(fC->Child(Hierarchical_identifier));
          } else if (fC->Type(Hierarchical_identifier) !=
                     VObjectType::paPs_or_hierarchical_identifier) {
            Hierarchical_identifier = Net_lvalue;
          }
          if (isSelected(fC, Hierarchical_identifier))
            bit_or_part_select = true;
          sigId = Hierarchical_identifier;
          if (fC->Type(fC->Child(sigId)) == VObjectType::slStringConst) {
            sigId = fC->Child(sigId);
          }
          sigName = fC->SymName(sigId);
        } else if (fC->Type(Net_lvalue) == VObjectType::paExpression) {
          NodeId Primary = fC->Child(Net_lvalue);
          NodeId Primary_literal = fC->Child(Primary);
          if (fC->Type(Primary_literal) == VObjectType::paComplex_func_call)
            bit_or_part_select = true;
          sigId = fC->Child(Primary_literal);
          sigName = fC->SymName(sigId);
        }
        if (ports) {
          if (index < ports->size()) {
            uhdm::Port* p = (*ports)[index];

            if ((!bit_or_part_select) &&
                (fC->Type(sigId) == VObjectType::slStringConst)) {
              uhdm::RefObj* ref = s.make<uhdm::RefObj>();
              fC->populateCoreMembers(sigId, sigId, ref);
              p->setHighConn(ref);
              ref->setParent(p, true);
              ref->setName(sigName);

            } else {
              uhdm::Any* exp = nullptr;
              if (fC->Type(Net_lvalue) == VObjectType::paNet_lvalue) {
                NodeId Hierarchical_identifier = fC->Child(Net_lvalue);
                if (fC->Type(fC->Child(Hierarchical_identifier)) ==
                    VObjectType::paHierarchical_identifier) {
                  Hierarchical_identifier =
                      fC->Child(fC->Child(Hierarchical_identifier));
                } else if (fC->Type(Hierarchical_identifier) !=
                           VObjectType::paPs_or_hierarchical_identifier) {
                  Hierarchical_identifier = Net_lvalue;
                }
                checkForLoops(true);
                exp = compileExpression(component, fC, Hierarchical_identifier,
                                        compileDesign, Reduce::No, p, nullptr);
                checkForLoops(false);
              } else {
                checkForLoops(true);
                exp = compileExpression(component, fC, Net_lvalue,
                                        compileDesign, Reduce::Yes, p, nullptr);
                checkForLoops(false);
              }
              if (exp != nullptr) {
                p->setHighConn(exp);
                exp->setParent(p, true);
              }
            }
          }
        }
        if ((inst_type == VObjectType::paCmos_switch_instance) ||
            (inst_type == VObjectType::paEnable_gate_instance) ||
            (inst_type == VObjectType::paMos_switch_instance) ||
            (inst_type == VObjectType::paN_input_gate_instance) ||
            (inst_type == VObjectType::paN_output_gate_instance) ||
            (inst_type == VObjectType::paPass_enable_switch_instance) ||
            (inst_type == VObjectType::paPass_switch_instance) ||
            (inst_type == VObjectType::paPull_gate_instance) ||
            (inst_type == VObjectType::paUdp_instantiation) ||
            (inst_type == VObjectType::paModule_instantiation)) {
          uhdm::Port* p = s.make<uhdm::Port>();
          p->setParent(pexpr);
          fC->populateCoreMembers(Net_lvalue, Net_lvalue, p);
          if ((fC->Type(sigId) == VObjectType::slStringConst) &&
              (!bit_or_part_select)) {
            uhdm::RefObj* ref = s.make<uhdm::RefObj>();
            fC->populateCoreMembers(sigId, sigId, ref);
            p->setHighConn(ref);
            ref->setName(sigName);
            ref->setParent(p, true);
          } else {
            NodeId Hierarchical_identifier = fC->Child(Net_lvalue);
            if (fC->Type(fC->Child(Hierarchical_identifier)) ==
                VObjectType::paHierarchical_identifier) {
              Hierarchical_identifier =
                  fC->Child(fC->Child(Hierarchical_identifier));
            } else if (fC->Type(Hierarchical_identifier) !=
                       VObjectType::paPs_or_hierarchical_identifier) {
              Hierarchical_identifier = Net_lvalue;
            }
            checkForLoops(true);
            if (uhdm::Any* exp = compileExpression(
                    component, fC, Hierarchical_identifier, compileDesign,
                    Reduce::No, nullptr, nullptr)) {
              p->setHighConn(exp);
              exp->setParent(p, true);
            }
            checkForLoops(false);
          }
          ports->emplace_back(p);
        }
        Net_lvalue = fC->Sibling(Net_lvalue);
        index++;
      }
    } else if (fC->Type(Net_lvalue) ==
               VObjectType::paList_of_port_connections) {
      /*
      n<TESTBENCH> u<195> t<StringConst> p<212> s<211> l<21>
      n<tb> u<196> t<StringConst> p<197> l<21>
      n<> u<197> t<Name_of_instance> p<211> c<196> s<210> l<21>
      n<observe> u<198> t<StringConst> p<203> s<202> l<21>
      n<o> u<199> t<StringConst> p<200> l<21>
      n<> u<200> t<Primary_literal> p<201> c<199> l<21>
      n<> u<201> t<Primary> p<202> c<200> l<21>
      n<> u<202> t<Expression> p<203> c<201> l<21>
      n<> u<203> t<Named_port_connection> p<210> c<198> s<209> l<21>
      n<drive> u<204> t<StringConst> p<209> s<208> l<21>
      n<i> u<205> t<StringConst> p<206> l<21>
      n<> u<206> t<Primary_literal> p<207> c<205> l<21>
      n<> u<207> t<Primary> p<208> c<206> l<21>
      n<> u<208> t<Expression> p<209> c<207> l<21>
      n<> u<209> t<Named_port_connection> p<210> c<204> l<21>
      n<> u<210> t<List_of_port_connections> p<211> c<203> l<21>
      n<> u<211> t<Hierarchical_instance> p<212> c<197> l<21>
      n<> u<212> t<Module_instantiation> p<213> c<195> l<21>
      */
      NodeId Named_port_connection = fC->Child(Net_lvalue);
      uint32_t index = 0;
      bool orderedConnection = false;
      if (fC->Type(Named_port_connection) ==
          VObjectType::paOrdered_port_connection) {
        orderedConnection = true;
      }

      bool wildcard = false;
      NodeId MemNamed_port_connection = Named_port_connection;
      uint32_t wildcardLineNumber = 0;
      uint16_t wildcardColumnNumber = 0;
      while (Named_port_connection) {
        NodeId formalId = fC->Child(Named_port_connection);
        if (fC->Type(formalId) == VObjectType::paDOTSTAR) {
          // .* connection
          wildcard = true;
          wildcardLineNumber = fC->Line(formalId);
          wildcardColumnNumber = fC->Column(formalId);
          break;
        }
        Named_port_connection = fC->Sibling(Named_port_connection);
      }

      Named_port_connection = MemNamed_port_connection;
      while (Named_port_connection) {
        NodeId formalId = fC->Child(Named_port_connection);
        if (!formalId) {
          Named_port_connection = fC->Sibling(Named_port_connection);
          index++;
          continue;
        }
        uhdm::AttributeCollection* attributes = nullptr;
        if (fC->Type(formalId) == VObjectType::paAttribute_instance) {
          attributes = compileAttributes(component, fC, formalId, compileDesign,
                                         nullptr);
          while (fC->Type(formalId) == VObjectType::paAttribute_instance) {
            formalId = fC->Sibling(formalId);
          }
        }
        if (fC->Type(formalId) == VObjectType::paDOTSTAR) {
          // .* connection
          Named_port_connection = fC->Sibling(Named_port_connection);
          continue;
        }

        NodeId sigId = formalId;
        std::string_view formalName = fC->SymName(formalId);
        NodeId Expression = fC->Sibling(formalId);
        if (orderedConnection) {
          Expression = formalId;
          NodeId Primary = fC->Child(Expression);
          NodeId Primary_literal = fC->Child(Primary);
          NodeId formalNameId = fC->Child(Primary_literal);
          formalName = fC->SymName(formalNameId);
        } else {
          NodeId tmp = Expression;
          if (fC->Type(tmp) == VObjectType::paOPEN_PARENS) {
            tmp = fC->Sibling(tmp);
            if (fC->Type(tmp) ==
                VObjectType::paCLOSE_PARENS) {  // .p()  explicit disconnect
              Named_port_connection = fC->Sibling(Named_port_connection);
              uhdm::Port* p = nullptr;

              if (index < ports->size()) {
                if (orderedConnection) {
                  formalName = signals[index]->getName();
                  p = (*ports)[index];
                } else {
                  for (uhdm::Port* pItr : *ports) {
                    if (pItr->getName() == formalName) {
                      p = pItr;
                      break;
                    }
                  }
                  if (p == nullptr) p = (*ports)[index];
                }
              }

              if (p == nullptr) {
                p = s.make<uhdm::Port>();
                p->setParent(pexpr);
                ports->emplace_back(p);
                p->setName(formalName);
                fC->populateCoreMembers(formalId, formalId, p);
              }

              if (!allSignalsConst.empty()) {
                auto found = allSignalsConst.find(p->getName());
                if (found == allSignalsConst.end()) {
                  SymbolTable* symbols = m_session->getSymbolTable();
                  ErrorContainer* errors = m_session->getErrorContainer();
                  Location loc(fileSystem->toPathId(p->getFile(), symbols),
                               p->getStartLine(), p->getStartColumn(),
                               symbols->registerSymbol(p->getName()));
                  errors->addError(ErrorDefinition::ELAB_UNKNOWN_PORT, loc);
                }
              }

              uhdm::Operation* op = s.make<uhdm::Operation>();
              op->setOpType(vpiNullOp);
              fC->populateCoreMembers(tmp, tmp, op);
              op->setParent(p, true);
              p->setHighConn(op);
              index++;
              continue;
            } else if (fC->Type(tmp) ==
                       VObjectType::paExpression) {  // .p(s) connection by name
              sigId = tmp;
              Expression = tmp;
              if (!allSignalsConst.empty()) {
                auto found = allSignalsConst.find(formalName);
                if (found == allSignalsConst.end()) {
                  SymbolTable* symbols = m_session->getSymbolTable();
                  ErrorContainer* errors = m_session->getErrorContainer();
                  Location loc(fC->getFileId(formalId), fC->Line(formalId),
                               fC->Column(formalId),
                               symbols->registerSymbol(formalName));
                  errors->addError(ErrorDefinition::ELAB_UNKNOWN_PORT, loc);
                }
              }
            }
          }  // else .p implicit connection
        }
        uhdm::Expr* hexpr = nullptr;
        if (fC->Type(Expression) == VObjectType::paAttribute_instance) {
          attributes = compileAttributes(component, fC, Expression,
                                         compileDesign, nullptr);
          while (fC->Type(Expression) == VObjectType::paAttribute_instance)
            Expression = fC->Sibling(Expression);
        }

        uhdm::Port* p = nullptr;
        if (index < ports->size()) {
          if (orderedConnection) {
            formalName = signals[index]->getName();
            p = (*ports)[index];
          } else {
            for (uhdm::Port* pItr : *ports) {
              if (pItr->getName() == formalName) {
                p = pItr;
                break;
              }
            }
            if (p == nullptr) p = (*ports)[index];
          }
        }

        if (p == nullptr) {
          p = s.make<uhdm::Port>();
          p->setParent(pexpr);
          ports->emplace_back(p);
        }

        if (Expression) {
          checkForLoops(true);
          hexpr = (uhdm::Expr*)compileExpression(component, fC, Expression,
                                                 compileDesign, Reduce::Yes, p,
                                                 nullptr);
          checkForLoops(false);
          NodeId Primary = fC->Child(Expression);
          NodeId Primary_literal = fC->Child(Primary);
          sigId = fC->Child(Primary_literal);
        }
        bool modPort = true;
        if (hexpr && hexpr->getUhdmType() == uhdm::UhdmType::HierPath) {
          uhdm::HierPath* hier = (uhdm::HierPath*)hexpr;
          for (auto p : *hier->getPathElems()) {
            if (p->getUhdmType() != uhdm::UhdmType::RefObj) {
              modPort = false;
              break;
            }
          }
        }

        std::string sigName;
        if (modPort && (fC->Type(sigId) == VObjectType::slStringConst)) {
          sigName = fC->SymName(sigId);
        }
        if (NodeId subId = fC->Sibling(sigId)) {
          if (fC->Name(subId)) {
            StrAppend(&sigName, ".", fC->SymName(subId));
          }
        }

        if ((!sigName.empty()) && (hexpr == nullptr)) {
          uhdm::RefObj* ref = s.make<uhdm::RefObj>();
          fC->populateCoreMembers(sigId, sigId, ref);
          ref->setName(sigName);
          ref->setParent(p, true);
          p->setHighConn(ref);

        } else if (hexpr != nullptr) {
          p->setHighConn(hexpr);
          hexpr->setParent(p);
          if (hexpr->getUhdmType() == uhdm::UhdmType::RefObj) {
            ((uhdm::RefObj*)hexpr)->setParent(p, true);
          }
        }
        p->setName(formalName);
        if (attributes) {
          p->setAttributes(attributes);
          for (auto a : *attributes) a->setParent(p);
        }
        fC->populateCoreMembers(formalId, formalId, p);
        // bool lowconn_is_nettype = false;
        if (const uhdm::Any* lc = p->getLowConn()) {
          if (lc->getUhdmType() == uhdm::UhdmType::RefObj) {
            uhdm::RefObj* rf = (uhdm::RefObj*)lc;
            fC->populateCoreMembers(formalId, formalId, rf);
            // const uhdm::Any* act = rf->getActualGroup();
            // if (act && (act->getUhdmType() == uhdm::UhdmType::LogicNet))
            //   lowconn_is_nettype = true;
          }
        }
        auto itr = allSignals.find(formalName);
        if (itr != allSignals.end()) {
          allSignals.erase(itr);
        }
        Named_port_connection = fC->Sibling(Named_port_connection);
        index++;
      }
      {
        uint32_t formalSize = 0;
        if (ports) {
          formalSize = ports->size();
        }
        if (wildcard) {
          // Add missing ports
          uhdm::PortCollection* newPorts = s.makeCollection<uhdm::Port>();
          for (Signal* s1 : signals) {
            const std::string_view sigName = s1->getName();
            bool found = false;
            uhdm::Port* pp = nullptr;
            for (uhdm::Port* p : *ports) {
              if (p->getName() == s1->getName()) {
                newPorts->emplace_back(p);
                found = true;
                pp = p;
                break;
              }
            }
            if (!found) {
              uhdm::Port* p = s.make<uhdm::Port>();
              p->setParent(pexpr);
              p->setName(sigName);
              p->setFile(fileSystem->toPath(fC->getFileId()));
              p->setStartLine(wildcardLineNumber);
              p->setStartColumn(wildcardColumnNumber);
              p->setEndLine(wildcardLineNumber);
              p->setEndColumn(wildcardColumnNumber + 1);
              newPorts->emplace_back(p);
              pp = p;
            }
            if (pp->getHighConn() == nullptr) {
              uhdm::RefObj* ref = s.make<uhdm::RefObj>();
              ref->setFile(fileSystem->toPath(fC->getFileId()));
              ref->setStartLine(wildcardLineNumber);
              ref->setStartColumn(wildcardColumnNumber);
              ref->setEndLine(wildcardLineNumber);
              ref->setEndColumn(wildcardColumnNumber + 1);
              ref->setName(sigName);
              ref->setParent(pp);

              pp->setHighConn(ref);
            }
          }
        } else if (index < formalSize) {
          // Add missing ports
          uhdm::PortCollection* newPorts = s.makeCollection<uhdm::Port>();
          for (Signal* s1 : signals) {
            const std::string_view sigName = s1->getName();

            auto itr = allSignals.find(sigName);
            if (itr != allSignals.end()) {
              const auto& pair = (*itr);
              uhdm::Port* p = nullptr;
              for (uhdm::Port* pt : *ports) {
                if (pt->getName() == sigName) {
                  p = pt;
                  newPorts->emplace_back(p);
                  break;
                }
              }

              if (p) {
                if (NodeId defaultId = pair.second->getDefaultValue()) {
                  checkForLoops(true);
                  if (uhdm::Expr* exp = (uhdm::Expr*)compileExpression(
                          component, fC, defaultId, compileDesign, Reduce::No,
                          p, nullptr)) {
                    p->setHighConn(exp);
                  }
                  checkForLoops(false);
                }
              }
            } else {
              for (uhdm::Port* pt : *ports) {
                if (pt->getName() == sigName) {
                  newPorts->emplace_back(pt);
                  break;
                }
              }
            }
          }
        }
      }
    }
  }
  // Finally any unconnected ports with default value gets assigned the value
  if (ports) {
    for (auto p : *ports) {
      if (p->getHighConn() != nullptr) continue;
      auto found = allSignals.find(p->getName());
      if (found == allSignals.end()) continue;
      if (NodeId defaultId = (*found).second->getDefaultValue()) {
        checkForLoops(true);
        if (uhdm::Expr* exp = (uhdm::Expr*)compileExpression(
                component, fC, defaultId, compileDesign, Reduce::No, p,
                nullptr)) {
          p->setHighConn(exp);
        }
        checkForLoops(false);
      }
    }
  }
}

uhdm::Initial* CompileHelper::compileInitialBlock(DesignComponent* component,
                                                  const FileContent* fC,
                                                  NodeId initial_construct,
                                                  CompileDesign* compileDesign,
                                                  uhdm::Any* pstmt) {
  uhdm::Serializer& s = compileDesign->getSerializer();
  compileDesign->lockSerializer();
  uhdm::Initial* init = s.make<uhdm::Initial>();
  init->setParent(pstmt);
  fC->populateCoreMembers(initial_construct, initial_construct, init);
  NodeId Statement_or_null = fC->Child(initial_construct);
  if (uhdm::AnyCollection* stmts = compileStmt(
          component, fC, Statement_or_null, compileDesign, Reduce::No, init)) {
    init->setStmt((*stmts)[0]);
  }
  compileDesign->unlockSerializer();
  return init;
}

uhdm::FinalStmt* CompileHelper::compileFinalBlock(DesignComponent* component,
                                                  const FileContent* fC,
                                                  NodeId final_construct,
                                                  CompileDesign* compileDesign,
                                                  uhdm::Any* pstmt) {
  uhdm::Serializer& s = compileDesign->getSerializer();
  compileDesign->lockSerializer();
  uhdm::FinalStmt* final = s.make<uhdm::FinalStmt>();
  final->setParent(pstmt);
  fC->populateCoreMembers(final_construct, final_construct, final);
  NodeId Statement_or_null = fC->Child(final_construct);
  if (uhdm::AnyCollection* stmts = compileStmt(
          component, fC, Statement_or_null, compileDesign, Reduce::No, final)) {
    final->setStmt((*stmts)[0]);
  }
  compileDesign->unlockSerializer();
  return final;
}

uhdm::AtomicStmt* CompileHelper::compileProceduralTimingControlStmt(
    DesignComponent* component, const FileContent* fC,
    NodeId Procedural_timing_control, CompileDesign* compileDesign,
    uhdm::Any* pstmt, ValuedComponentI* instance) {
  uhdm::Serializer& s = compileDesign->getSerializer();
  /*
  n<#100> u<70> t<IntConst> p<71> l<7>
  n<> u<71> t<Delay_control> p<72> c<70> l<7>
  n<> u<72> t<Procedural_timing_control> p<88> c<71> s<87> l<7>
  */

  NodeId Delay_control = fC->Child(Procedural_timing_control);
  if (fC->Type(Delay_control) == VObjectType::paEvent_control) {
    return compileEventControlStmt(component, fC, Procedural_timing_control,
                                   compileDesign, pstmt, instance);
  }
  NodeId IntConst = fC->Child(Delay_control);
  uhdm::DelayControl* dc = s.make<uhdm::DelayControl>();
  std::string_view value = fC->SymName(IntConst);
  if (value.front() == '#') {
    dc->setVpiDelay(value);
  } else {
    auto childIds =
        fC->sl_collect_all(IntConst,
                           {VObjectType::slStringConst, VObjectType::slIntConst,
                            VObjectType::slRealConst},
                           true);
    NodeId valueNodeId = childIds.empty() ? IntConst : childIds.front();
    if (fC->Type(valueNodeId) == VObjectType::slStringConst) {
      uhdm::RefObj* ref = s.make<uhdm::RefObj>();
      ref->setName(fC->SymName(valueNodeId));
      ref->setParent(dc);
      fC->populateCoreMembers(valueNodeId, valueNodeId, ref);
      dc->setDelay(ref);
    } else if ((fC->Type(valueNodeId) == VObjectType::slIntConst) ||
               (fC->Type(valueNodeId) == VObjectType::slRealConst)) {
      uhdm::Constant* c = s.make<uhdm::Constant>();
      std::string value =
          (fC->Type(valueNodeId) == VObjectType::slIntConst) ? "INT:" : "REAL:";
      value.append(fC->SymName(valueNodeId));
      c->setValue(value);
      c->setDecompile(fC->SymName(valueNodeId));
      c->setSize(64);
      c->setConstType(fC->Type(valueNodeId) == VObjectType::slIntConst
                          ? vpiIntConst
                          : vpiRealConst);
      c->setParent(dc);
      fC->populateCoreMembers(valueNodeId, valueNodeId, c);
      dc->setDelay(c);
    }
  }
  fC->populateCoreMembers(Delay_control, Delay_control, dc);
  if (NodeId Statement_or_null = fC->Sibling(Procedural_timing_control)) {
    if (uhdm::AnyCollection* st =
            compileStmt(component, fC, Statement_or_null, compileDesign,
                        Reduce::No, dc, instance)) {
      uhdm::Any* stmt = st->front();
      dc->setStmt(stmt);
      stmt->setParent(dc);
      dc->setEndLine(stmt->getEndLine());
      dc->setEndColumn(stmt->getEndColumn());
    } else {
      // Malformed AST due to grammar for: #1 t
      if (NodeId unit = fC->Child(IntConst)) {
        unit = fC->Child(unit);  // StringConst child of Instance_name
        const std::string_view name = fC->SymName(unit);
        std::pair<uhdm::TaskFunc*, DesignComponent*> ret =
            getTaskFunc(name, component, compileDesign, nullptr, nullptr);
        uhdm::TaskFunc* tf = ret.first;
        uhdm::Any* call = nullptr;
        if (tf) {
          if (tf->getUhdmType() == uhdm::UhdmType::Function) {
            uhdm::FuncCall* fcall = s.make<uhdm::FuncCall>();
            fcall->setFunction(any_cast<uhdm::Function>(tf));
            call = fcall;
          } else {
            uhdm::TaskCall* tcall = s.make<uhdm::TaskCall>();
            tcall->setTask(any_cast<uhdm::Task>(tf));
            call = tcall;
          }
        }
        if (call) {
          NodeId nid = fC->Child(unit);
          if (!nid) nid = unit;
          fC->populateCoreMembers(nid, nid, call);
          dc->setStmt(call);
          call->setParent(dc);
          if (fC->Child(unit)) {
            dc->setEndLine(call->getEndLine());
            dc->setEndColumn(call->getEndColumn());
          }
        }
      }
    }
  }
  return dc;
}

uhdm::AtomicStmt* CompileHelper::compileDelayControl(
    DesignComponent* component, const FileContent* fC,
    NodeId Procedural_timing_control, CompileDesign* compileDesign,
    uhdm::Any* pexpr, ValuedComponentI* instance) {
  uhdm::Serializer& s = compileDesign->getSerializer();

  NodeId Delay_control = fC->Child(Procedural_timing_control);
  if (fC->Type(Delay_control) == VObjectType::paEvent_control) {
    return compileEventControlStmt(component, fC, Procedural_timing_control,
                                   compileDesign, pexpr, instance);
  }
  NodeId IntConst = fC->Child(Delay_control);
  const std::string_view value = fC->SymName(IntConst);
  uhdm::DelayControl* dc = s.make<uhdm::DelayControl>();
  dc->setVpiDelay(value);
  dc->setParent(pexpr);
  fC->populateCoreMembers(fC->Child(Delay_control), fC->Child(Delay_control),
                          dc);
  return dc;
}

uhdm::Always* CompileHelper::compileAlwaysBlock(DesignComponent* component,
                                                const FileContent* fC,
                                                NodeId id,
                                                CompileDesign* compileDesign,
                                                uhdm::Any* pstmt,
                                                ValuedComponentI* instance) {
  uhdm::Serializer& s = compileDesign->getSerializer();
  compileDesign->lockSerializer();
  uhdm::Always* always = s.make<uhdm::Always>();
  always->setParent(pstmt);
  NodeId always_keyword = fC->Child(id);
  switch (fC->Type(always_keyword)) {
    case VObjectType::paALWAYS:
      always->setAlwaysType(vpiAlways);
      break;
    case VObjectType::paALWAYS_COMB:
      always->setAlwaysType(vpiAlwaysComb);
      break;
    case VObjectType::paALWAYS_FF:
      always->setAlwaysType(vpiAlwaysFF);
      break;
    case VObjectType::paALWAYS_LATCH:
      always->setAlwaysType(vpiAlwaysLatch);
      break;
    default:
      break;
  }
  NodeId Statement = fC->Sibling(always_keyword);
  NodeId Statement_item = fC->Child(Statement);
  uhdm::AnyCollection* stmts = nullptr;
  if (fC->Type(Statement_item) == VObjectType::slStringConst) {
    stmts = compileStmt(component, fC, Statement_item, compileDesign,
                        Reduce::No, always, instance);
  } else {
    NodeId the_stmt = fC->Child(Statement_item);
    stmts = compileStmt(component, fC, the_stmt, compileDesign, Reduce::No,
                        always, instance);
  }
  if (stmts) {
    uhdm::Any* stmt = (*stmts)[0];
    always->setStmt(stmt);
    stmt->setParent(always);
  }

  fC->populateCoreMembers(id, id, always);
  compileDesign->unlockSerializer();
  return always;
}

bool CompileHelper::isMultidimensional(uhdm::Typespec* ts,
                                       DesignComponent* component) {
  bool isMultiDimension = false;
  if (ts) {
    uhdm::UhdmType ttps = ts->getUhdmType();
    if (ttps == uhdm::UhdmType::LogicTypespec) {
      uhdm::LogicTypespec* lts = (uhdm::LogicTypespec*)ts;
      // if (component && valuedcomponenti_cast<Package>(component)) {
      //   if (lts->getRanges() && !lts->getRanges()->empty()) isMultiDimension
      //   = true;
      // } else {
      if (lts->getRanges() && lts->getRanges()->size() > 1)
        isMultiDimension = true;
      //}
    } else if (ttps == uhdm::UhdmType::ArrayTypespec) {
      uhdm::ArrayTypespec* lts = (uhdm::ArrayTypespec*)ts;
      if (lts->getRanges() && lts->getRanges()->size() > 1)
        isMultiDimension = true;
    } else if (ttps == uhdm::UhdmType::PackedArrayTypespec) {
      uhdm::PackedArrayTypespec* lts = (uhdm::PackedArrayTypespec*)ts;
      if (lts->getElemTypespec() && lts->getElemTypespec()->getActual() &&
          (lts->getElemTypespec()->getActual()->getUhdmType() ==
           uhdm::UhdmType::StructTypespec)) {
        isMultiDimension = true;
      } else {
        if (lts->getRanges() && lts->getRanges()->size() > 1)
          isMultiDimension = true;
      }
    } else if (ttps == uhdm::UhdmType::BitTypespec) {
      uhdm::BitTypespec* lts = (uhdm::BitTypespec*)ts;
      if (lts->getRanges() && lts->getRanges()->size() > 1)
        isMultiDimension = true;
    } else if (ttps == uhdm::UhdmType::StructTypespec) {
      isMultiDimension = true;
    }
  }
  return isMultiDimension;
}

bool CompileHelper::isDecreasingRange(uhdm::Typespec* ts,
                                      DesignComponent* component) {
  if (ts) {
    uhdm::UhdmType ttps = ts->getUhdmType();
    uhdm::Range* r = nullptr;
    if (ttps == uhdm::UhdmType::LogicTypespec) {
      uhdm::LogicTypespec* lts = (uhdm::LogicTypespec*)ts;
      if (lts->getRanges() && !lts->getRanges()->empty()) {
        r = (*lts->getRanges())[0];
      }
    } else if (ttps == uhdm::UhdmType::ArrayTypespec) {
      uhdm::ArrayTypespec* lts = (uhdm::ArrayTypespec*)ts;
      if (lts->getRanges() && !lts->getRanges()->empty()) {
        r = (*lts->getRanges())[0];
      }
    } else if (ttps == uhdm::UhdmType::PackedArrayTypespec) {
      uhdm::PackedArrayTypespec* lts = (uhdm::PackedArrayTypespec*)ts;
      if (lts->getRanges() && !lts->getRanges()->empty()) {
        r = (*lts->getRanges())[0];
      }
    } else if (ttps == uhdm::UhdmType::BitTypespec) {
      uhdm::BitTypespec* lts = (uhdm::BitTypespec*)ts;
      if (lts->getRanges() && !lts->getRanges()->empty()) {
        r = (*lts->getRanges())[0];
      }
    }
    if (r) {
      bool invalidValue = false;
      uhdm::ExprEval eval;
      int64_t lv = eval.get_value(invalidValue, r->getLeftExpr());
      int64_t rv = eval.get_value(invalidValue, r->getRightExpr());
      if ((invalidValue == false) && (lv > rv)) return true;
    }
  }
  return false;
}

uhdm::Any* CompileHelper::defaultPatternAssignment(
    const uhdm::Typespec* tps, uhdm::Any* exp, DesignComponent* component,
    CompileDesign* compileDesign, Reduce reduce, ValuedComponentI* instance) {
  uhdm::Any* result = exp;
  if (tps == nullptr) {
    return result;
  }
  if (exp == nullptr) {
    return result;
  }
  uhdm::Serializer& s = compileDesign->getSerializer();
  FileSystem* const fileSystem = m_session->getFileSystem();
  SymbolTable* const symbols = m_session->getSymbolTable();
  bool invalidValue = false;
  int32_t ncsize = 32;
  uhdm::Range* r = nullptr;
  uhdm::UhdmType ttps = tps->getUhdmType();
  uhdm::UhdmType baseType = uhdm::UhdmType::IntTypespec;
  if (ttps == uhdm::UhdmType::LogicTypespec) {
    uhdm::LogicTypespec* lts = (uhdm::LogicTypespec*)tps;
    baseType = uhdm::UhdmType::LogicTypespec;
    if (lts->getRanges() && !lts->getRanges()->empty()) {
      r = (*lts->getRanges())[0];
    }
    ncsize = 1;
  } else if (ttps == uhdm::UhdmType::ArrayTypespec) {
    uhdm::ArrayTypespec* lts = (uhdm::ArrayTypespec*)tps;
    uhdm::Typespec* ets = nullptr;
    if (uhdm::RefTypespec* rt = lts->getElemTypespec()) {
      ets = rt->getActual();
    }
    if (ets != nullptr) {
      baseType = ets->getUhdmType();
      if (lts->getRanges() && !lts->getRanges()->empty()) {
        r = (*lts->getRanges())[0];
      }
      ncsize = Bits(ets, invalidValue, component, compileDesign, Reduce::Yes,
                    instance, fileSystem->toPathId(ets->getFile(), symbols),
                    ets->getStartLine(), false);
    }
  } else if (ttps == uhdm::UhdmType::PackedArrayTypespec) {
    uhdm::PackedArrayTypespec* lts = (uhdm::PackedArrayTypespec*)tps;
    uhdm::Typespec* ets = nullptr;
    if (uhdm::RefTypespec* rt = lts->getElemTypespec()) {
      ets = rt->getActual();
    }
    if (ets != nullptr) {
      baseType = ets->getUhdmType();
      if (lts->getRanges() && !lts->getRanges()->empty()) {
        r = (*lts->getRanges())[0];
      }
      ncsize = Bits(ets, invalidValue, component, compileDesign, Reduce::Yes,
                    instance, fileSystem->toPathId(ets->getFile(), symbols),
                    ets->getStartLine(), false);
    }
  } else if (ttps == uhdm::UhdmType::BitTypespec) {
    uhdm::BitTypespec* lts = (uhdm::BitTypespec*)tps;
    baseType = uhdm::UhdmType::BitTypespec;
    if (lts->getRanges() && !lts->getRanges()->empty()) {
      r = (*lts->getRanges())[0];
    }
    ncsize = 1;
  } else if (ttps == uhdm::UhdmType::IntTypespec) {
    ncsize = 32;
  } else if (ttps == uhdm::UhdmType::IntegerTypespec) {
    ncsize = 32;
  } else if (ttps == uhdm::UhdmType::ShortIntTypespec) {
    ncsize = 16;
  } else if (ttps == uhdm::UhdmType::ByteTypespec) {
    ncsize = 8;
  }

  if (exp->getUhdmType() == uhdm::UhdmType::Operation) {
    uhdm::Operation* op = (uhdm::Operation*)exp;
    uhdm::AnyCollection* operands = op->getOperands();
    int32_t opType = op->getOpType();
    switch (opType) {
      case vpiCastOp: {
        const uhdm::Typespec* optps = nullptr;
        if (const uhdm::RefTypespec* rt = op->getTypespec()) {
          optps = rt->getActual();
        }
        if (optps == nullptr) break;
        uhdm::UhdmType ottps = optps->getUhdmType();
        uhdm::Any* op0 = (*operands)[0];
        if (op0->getUhdmType() == uhdm::UhdmType::Operation) {
          uhdm::Operation* oper0 = (uhdm::Operation*)op0;
          int32_t op0Type = oper0->getOpType();
          if (op0Type == vpiConcatOp) {
            uhdm::AnyCollection* operandsConcat = oper0->getOperands();
            uhdm::Any* op0Concat = (*operandsConcat)[0];
            if ((m_reduce == Reduce::Yes) && (reduce == Reduce::Yes) &&
                (op0Concat->getName() == "default")) {
              bool invalidValue = false;
              uhdm::ExprEval eval;
              uint64_t val0 = eval.get_value(invalidValue,
                                             (uhdm::Expr*)(*operandsConcat)[1]);
              uhdm::Constant* c = s.make<uhdm::Constant>();
              if (ottps == uhdm::UhdmType::IntTypespec) {
                uhdm::IntTypespec* itps = (uhdm::IntTypespec*)optps;
                if (itps->getSigned()) {
                  if (val0 == 1) {
                    c->setDecompile(std::to_string(-1));
                    c->setValue("INT:" + std::to_string(-1));
                    c->setSize(32);
                    c->setConstType(vpiIntConst);
                    result = c;
                  } else {
                    c->setDecompile(std::to_string(0));
                    c->setValue("INT:" + std::to_string(0));
                    c->setSize(32);
                    c->setConstType(vpiIntConst);
                    result = c;
                  }
                } else {
                  if (val0 == 1) {
                    c->setDecompile(std::to_string(UINT_MAX));
                    c->setValue("UINT:" + std::to_string(UINT_MAX));
                    c->setSize(32);
                    c->setConstType(vpiUIntConst);
                    result = c;
                  } else {
                    c->setDecompile(std::to_string(0));
                    c->setValue("UINT:" + std::to_string(0));
                    c->setSize(32);
                    c->setConstType(vpiUIntConst);
                    result = c;
                  }
                }
              }
            }
          }
        }
        break;
      }
      case vpiAssignmentPatternOp: {
        uhdm::Any* op0 = (*operands)[0];
        if (op0->getUhdmType() == uhdm::UhdmType::TaggedPattern) {
          uhdm::TaggedPattern* pattern = (uhdm::TaggedPattern*)op0;
          const uhdm::Typespec* ptps = nullptr;
          if (const uhdm::RefTypespec* rt = pattern->getTypespec()) {
            ptps = rt->getActual();
          }
          if ((m_reduce == Reduce::Yes) && (reduce == Reduce::Yes) &&
              (ptps->getName() == "default")) {
            uhdm::Expr* expat = (uhdm::Expr*)pattern->getPattern();
            uhdm::Constant* c = any_cast<uhdm::Constant>(expat);
            int32_t psize = expat->getSize();
            if (psize == -1) {
              adjustUnsized(c, ncsize);
              c->setSize(ncsize);
            } else {
              if (ncsize < c->getSize()) c->setSize(ncsize);
            }
            if (r) {
              bool invalidValue = false;
              uhdm::Expr* lexp =
                  reduceExpr((uhdm::Expr*)r->getLeftExpr(), invalidValue,
                             component, compileDesign, instance,
                             fileSystem->toPathId(r->getFile(), symbols),
                             r->getStartLine(), nullptr);
              uhdm::Expr* rexp =
                  reduceExpr((uhdm::Expr*)r->getRightExpr(), invalidValue,
                             component, compileDesign, instance,
                             fileSystem->toPathId(r->getFile(), symbols),
                             r->getStartLine(), nullptr);
              uhdm::ExprEval eval;
              uint64_t lv = eval.get_uvalue(invalidValue, lexp);
              uint64_t rv = eval.get_uvalue(invalidValue, rexp);
              if (invalidValue == false) {
                uint32_t max = std::max(lv, rv);
                uint32_t min = std::min(lv, rv);
                uint32_t size = max - min + 1;
                if (baseType == uhdm::UhdmType::IntTypespec) {
                  uhdm::ArrayExpr* array = s.make<uhdm::ArrayExpr>();
                  uhdm::ExprCollection* exprs = array->getExprs(true);
                  for (uint32_t i = 0; i < size; i++) {
                    exprs->emplace_back(c);
                  }
                  result = array;
                }
              }
            }
          }
        }
        break;
      }
      case vpiMultiAssignmentPatternOp: {
        uhdm::Any* op1 = operands->at(1);
        if (op1->getUhdmType() == uhdm::UhdmType::Operation) {
          uhdm::Operation* oper = (uhdm::Operation*)op1;
          if (oper->getOpType() == vpiConcatOp) {
            uhdm::AnyCollection* opers = oper->getOperands();
            uhdm::Constant* c = any_cast<uhdm::Constant>(opers->at(0));
            if (c) {
              int32_t psize = c->getSize();
              if (psize == -1) {
                adjustUnsized(c, ncsize);
                c->setSize(ncsize);
              }
            }
          }
        }
        break;
      }
      default:
        break;
    }
  }

  return result;
}

bool CompileHelper::compileParameterDeclaration(
    DesignComponent* component, const FileContent* fC, NodeId nodeId,
    CompileDesign* compileDesign, Reduce reduce, bool localParam,
    ValuedComponentI* instance, bool port_param, bool muteErrors) {
  uhdm::Serializer& s = compileDesign->getSerializer();
  compileDesign->lockSerializer();
  std::vector<uhdm::Any*>* parameters = component->getParameters();
  if (parameters == nullptr) {
    component->setParameters(s.makeCollection<uhdm::Any>());
    parameters = component->getParameters();
  }
  uhdm::ParamAssignCollection* param_assigns = component->getParamAssigns();
  if (param_assigns == nullptr) {
    component->setParam_assigns(s.makeCollection<uhdm::ParamAssign>());
    param_assigns = component->getParamAssigns();
  }
  uhdm::Any* const pany = component->getUhdmModel();
  if (fC->Type(nodeId) == VObjectType::paList_of_type_assignments) {
    // Type param
    NodeId typeNameId = fC->Child(nodeId);
    while (typeNameId) {
      NodeId ntype = fC->Sibling(typeNameId);
      bool skip = false;
      if (ntype && fC->Type(ntype) == VObjectType::paData_type) {
        ntype = fC->Child(ntype);
        if (fC->Type(ntype) == VObjectType::paVIRTUAL)
          ntype = fC->Sibling(ntype);
        skip = true;
      } else {
        ntype = InvalidNodeId;
      }
      uhdm::TypeParameter* p = s.make<uhdm::TypeParameter>();
      p->setName(fC->SymName(typeNameId));
      fC->populateCoreMembers(typeNameId, typeNameId, p);
      if (uhdm::Typespec* tps =
              compileTypespec(component, fC, ntype, compileDesign, Reduce::No,
                              p, nullptr, false)) {
        if (p->getTypespec() == nullptr) {
          uhdm::RefTypespec* tpsRef = s.make<uhdm::RefTypespec>();
          tpsRef->setName(tps->getName());
          fC->populateCoreMembers(ntype, ntype, tpsRef);
          tpsRef->setParent(p);
          p->setTypespec(tpsRef);
        }
        p->getTypespec()->setActual(tps);
        tps->setParent(p);
      }
      if (localParam) {
        p->setLocalParam(true);
      }
      parameters->emplace_back(p);
      Parameter* param = new Parameter(fC, typeNameId, fC->SymName(typeNameId),
                                       ntype, port_param);
      param->setTypeParam();
      param->setUhdmParam(p);
      p->setParent(pany);
      component->insertParameter(param);
      typeNameId = fC->Sibling(typeNameId);
      if (skip) typeNameId = fC->Sibling(typeNameId);
    }

  } else if (fC->Type(nodeId) == VObjectType::paTYPE) {
    // Type param
    NodeId list_of_param_assignments = fC->Sibling(nodeId);
    NodeId Param_assignment = fC->Child(list_of_param_assignments);
    while (Param_assignment) {
      NodeId Identifier = fC->Child(Param_assignment);
      NodeId Constant_param_expression = fC->Sibling(Identifier);
      uhdm::TypeParameter* p = s.make<uhdm::TypeParameter>();
      p->setName(fC->SymName(Identifier));
      p->setParent(pany);
      fC->populateCoreMembers(Identifier, Identifier, p);
      NodeId Data_type = fC->Child(Constant_param_expression);
      if (uhdm::Typespec* tps =
              compileTypespec(component, fC, Data_type, compileDesign,
                              Reduce::No, p, nullptr, false)) {
        if (p->getTypespec() == nullptr) {
          uhdm::RefTypespec* tpsRef = s.make<uhdm::RefTypespec>();
          tpsRef->setName(tps->getName());
          fC->populateCoreMembers(Data_type, Data_type, tpsRef);
          tpsRef->setParent(p);
          p->setTypespec(tpsRef);
        }
        p->getTypespec()->setActual(tps);
        tps->setParent(p);
      }
      if (localParam) {
        p->setLocalParam(true);
      }
      parameters->emplace_back(p);
      Parameter* param = new Parameter(fC, Identifier, fC->SymName(Identifier),
                                       Constant_param_expression, port_param);
      param->setTypeParam();
      param->setUhdmParam(p);
      component->insertParameter(param);
      Param_assignment = fC->Sibling(Param_assignment);
    }
  } else {
    // Regular param
    NodeId Data_type_or_implicit;
    NodeId List_of_param_assignments;
    if (fC->Type(nodeId) == VObjectType::paList_of_param_assignments) {
      List_of_param_assignments = nodeId;
    } else {
      Data_type_or_implicit = fC->Child(nodeId);
      List_of_param_assignments = fC->Sibling(Data_type_or_implicit);
    }

    NodeId Param_assignment = fC->Child(List_of_param_assignments);
    while (Param_assignment) {
      uhdm::Typespec* ts = nullptr;
      if (Data_type_or_implicit) {
        ts = compileTypespec(component, fC, fC->Child(Data_type_or_implicit),
                             compileDesign, reduce, pany, instance, false);
      }
      bool isSigned = false;
      NodeId Data_type = fC->Child(Data_type_or_implicit);
      NodeId Data_typeId = Data_type;
      VObjectType the_type = fC->Type(Data_type);
      if (the_type == VObjectType::paData_type) {
        Data_type = fC->Child(Data_type);
        NodeId Signage = fC->Sibling(Data_type);
        VObjectType type = fC->Type(Data_type);
        if (type == VObjectType::paIntegerAtomType_Byte ||
            type == VObjectType::paIntegerAtomType_Int ||
            type == VObjectType::paIntegerAtomType_Integer ||
            type == VObjectType::paIntegerAtomType_LongInt ||
            type == VObjectType::paIntegerAtomType_Shortint ||
            type == VObjectType::paReal_number) {
          isSigned = true;
        }
        if (fC->Type(Signage) == VObjectType::paSigning_Signed) isSigned = true;
        if (fC->Type(Signage) == VObjectType::paSigning_Unsigned)
          isSigned = false;
      }

      bool isMultiDimension = isMultidimensional(ts, component);
      bool isDecreasing = isDecreasingRange(ts, component);

      NodeId name = fC->Child(Param_assignment);
      NodeId value = fC->Sibling(name);

      uhdm::Parameter* param = s.make<uhdm::Parameter>();
      param->setParent(pany);
      fC->populateCoreMembers(Param_assignment, Param_assignment, param);
      Parameter* p =
          new Parameter(fC, name, fC->SymName(name),
                        fC->Child(Data_type_or_implicit), port_param);

      // Unpacked dimensions
      if (fC->Type(value) == VObjectType::paUnpacked_dimension) {
        int32_t unpackedSize;
        std::vector<uhdm::Range*>* unpackedDimensions =
            compileRanges(component, fC, value, compileDesign, reduce, param,
                          instance, unpackedSize, muteErrors);
        param->setRanges(unpackedDimensions);
        param->setSize(unpackedSize);
        uhdm::ArrayTypespec* atps = s.make<uhdm::ArrayTypespec>();
        uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
        tsRef->setName(fC->SymName(Data_typeId));
        tsRef->setParent(atps);
        tsRef->setActual(ts);
        fC->populateCoreMembers(Data_typeId, Data_typeId, tsRef);
        atps->setElemTypespec(tsRef);
        uhdm::RefTypespec* atpsRef = s.make<uhdm::RefTypespec>();
        atpsRef->setParent(param);
        atpsRef->setActual(atps);
        fC->populateCoreMembers(Data_typeId, Data_typeId, atpsRef);
        param->setTypespec(atpsRef);
        p->setTypespec(atps);
        fC->populateCoreMembers(value, value, atps);
        atps->setRanges(unpackedDimensions);
        while (fC->Type(value) == VObjectType::paUnpacked_dimension) {
          value = fC->Sibling(value);
        }
        ts = atps;
        isMultiDimension = true;
      }

      const std::string_view the_name = fC->SymName(name);
      NodeId actual_value = value;

      if ((valuedcomponenti_cast<Package>(component) ||
           valuedcomponenti_cast<FileContent*>(component)) &&
          (instance == nullptr)) {
        if (!isMultiDimension) {
          // Check the RHS, we don't want to
          NodeId pattAssign = fC->sl_collect(
              actual_value, VObjectType::paConstant_concatenation);
          if (pattAssign != InvalidNodeId) {
            if (!m_session->getCommandLineParser()->reportNonSynthesizable()) {
              // More constant pushing with Synth option on
              isMultiDimension = true;
            }
          }
        }
        uhdm::Any* expr = compileExpression(
            component, fC, actual_value, compileDesign,
            isMultiDimension ? Reduce::No : reduce, param, nullptr);
        uhdm::UhdmType exprType = uhdm::UhdmType::BaseClass;
        if (expr != nullptr) {
          exprType = expr->getUhdmType();
          if ((expr = defaultPatternAssignment(
                   ts, expr, component, compileDesign, reduce, instance))) {
            exprType = expr->getUhdmType();
          }
        }
        if (expr && (exprType == uhdm::UhdmType::ArrayExpr)) {
          component->setComplexValue(the_name, (uhdm::Expr*)expr);
        } else if (expr && (exprType == uhdm::UhdmType::Constant)) {
          uhdm::Constant* c = (uhdm::Constant*)expr;
          if (c->getTypespec() == nullptr) {
            uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
            tsRef->setParent(c);
            tsRef->setActual(ts);
            c->setTypespec(tsRef);
          }
          int32_t size = c->getSize();
          if (ts) {
            bool invalidValue = false;
            int32_t sizetmp =
                Bits(ts, invalidValue, component, compileDesign, Reduce::Yes,
                     instance, fC->getFileId(), fC->Line(actual_value), false);
            if (!invalidValue) size = sizetmp;
          }
          adjustSize(ts, component, compileDesign, instance, c);
          Value* val = m_exprBuilder.fromVpiValue(c->getValue(), size);
          component->setValue(the_name, val, m_exprBuilder);
        } else if ((m_reduce == Reduce::Yes) && (reduce == Reduce::Yes) &&
                   (!isMultiDimension)) {
          uhdm::Expr* the_expr = (uhdm::Expr*)expr;
          if (the_expr->getTypespec() == nullptr) {
            uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
            tsRef->setParent(the_expr);
            tsRef->setActual(ts);
            the_expr->setTypespec(tsRef);
          }
          ExprEval expr_eval(the_expr, instance, fC->getFileId(),
                             fC->Line(name), nullptr);
          component->scheduleParamExprEval(the_name, expr_eval);
        } else if (expr && ((exprType == uhdm::UhdmType::Operation) ||
                            (exprType == uhdm::UhdmType::FuncCall) ||
                            (exprType == uhdm::UhdmType::SysFuncCall))) {
          component->setComplexValue(the_name, (uhdm::Expr*)expr);
          uhdm::Expr* the_expr = (uhdm::Expr*)expr;
          if (the_expr->getTypespec() == nullptr) {
            uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
            tsRef->setParent(the_expr);
            tsRef->setActual(ts);
            the_expr->setTypespec(tsRef);
          }
          if (isDecreasing &&
              (expr->getUhdmType() == uhdm::UhdmType::Operation)) {
            uhdm::Operation* op = (uhdm::Operation*)expr;
            int32_t optype = op->getOpType();
            if (optype == vpiAssignmentPatternOp || optype == vpiConcatOp) {
              uhdm::AnyCollection* operands = op->getOperands();
              if (operands && !operands->empty()) {
                if ((*operands)[0]->getUhdmType() == uhdm::UhdmType::RefObj) {
                  op->setReordered(true);
                  std::reverse(operands->begin(), operands->end());
                }
              }
            }
          }
        } else if (Value* val = m_exprBuilder.evalExpr(
                       fC, actual_value,
                       component)) {  // This call to create an error
          component->setValue(the_name, val, m_exprBuilder);
        }
      }
      p->setUhdmParam(param);
      p->setTypespec(ts);
      if (isMultiDimension) p->setMultidimension();
      component->insertParameter(p);

      if (ts) {
        if (param->getTypespec() == nullptr) {
          uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
          tsRef->setParent(param);
          fC->populateCoreMembers(Data_typeId, Data_typeId, tsRef);
          tsRef->setName(fC->SymName(Data_typeId));
          param->setTypespec(tsRef);
        }
        param->getTypespec()->setActual(ts);
        ts->setParent(param);
      }
      param->setSigned(isSigned);
      fC->populateCoreMembers(name, name, param);
      param->setName(fC->SymName(name));

      if (localParam) {
        param->setLocalParam(true);
      }
      parameters->emplace_back(param);

      ParamAssign* assign =
          new ParamAssign(fC, name, value, isMultiDimension, port_param);
      uhdm::ParamAssign* param_assign = s.make<uhdm::ParamAssign>();
      assign->setUhdmParamAssign(param_assign);
      component->addParamAssign(assign);
      param_assign->setParent(pany);
      fC->populateCoreMembers(Param_assignment, Param_assignment, param_assign);
      param_assigns->emplace_back(param_assign);
      param_assign->setLhs(param);
      param->setParent(param_assign);

      if (value) {
        // Unelaborated parameters
        if ((valuedcomponenti_cast<Package>(component) ||
             valuedcomponenti_cast<FileContent*>(component)) &&
            (instance == nullptr)) {
          uhdm::Expr* rhs = (uhdm::Expr*)compileExpression(
              component, fC, value, compileDesign, Reduce::No, param_assign,
              instance);
          rhs = (uhdm::Expr*)defaultPatternAssignment(
              ts, rhs, component, compileDesign, reduce, instance);
          param_assign->setLhs(param);
          if (rhs != nullptr) {
            rhs->setParent(param_assign);
            param_assign->setRhs(rhs);
          }
          uhdm::ParamAssignCollection* orig_param_assigns =
              component->getOrigParam_assigns();
          if (orig_param_assigns == nullptr) {
            component->setOrigParam_assigns(
                s.makeCollection<uhdm::ParamAssign>());
            orig_param_assigns = component->getOrigParam_assigns();
          }
          orig_param_assigns->emplace_back(param_assign);
        }

        uhdm::Expr* rhs = (uhdm::Expr*)compileExpression(
            component, fC, value, compileDesign,
            isMultiDimension ? Reduce::No : reduce, param_assign, instance);
        if ((m_reduce == Reduce::Yes) && (reduce == Reduce::Yes)) {
          rhs = (uhdm::Expr*)defaultPatternAssignment(
              ts, rhs, component, compileDesign, reduce, instance);
        }
        if (isDecreasing) {
          if (rhs->getUhdmType() == uhdm::UhdmType::Operation) {
            uhdm::Operation* op = (uhdm::Operation*)rhs;
            int32_t optype = op->getOpType();
            if (optype == vpiAssignmentPatternOp || optype == vpiConcatOp) {
              uhdm::AnyCollection* operands = op->getOperands();
              if (operands && !operands->empty()) {
                if ((*operands)[0]->getUhdmType() == uhdm::UhdmType::RefObj) {
                  op->setReordered(true);
                  std::reverse(operands->begin(), operands->end());
                }
              }
            }
          }
        }
        if ((m_elaborate == Elaborate::Yes) && rhs &&
            (rhs->getUhdmType() == uhdm::UhdmType::Constant)) {
          uhdm::Constant* c = (uhdm::Constant*)rhs;
          if (ts == nullptr) {
            switch (c->getConstType()) {
              case vpiRealConst: {
                ts = s.make<uhdm::RealTypespec>();
                ts->setParent(pany);
                p->setTypespec(ts);
                if (param->getTypespec() == nullptr) {
                  uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
                  tsRef->setParent(param);
                  param->setTypespec(tsRef);
                }
                param->getTypespec()->setActual(ts);
                break;
              }
              case vpiDecConst: {
                break;
              }
              case vpiIntConst: {
                uhdm::IntTypespec* its = s.make<uhdm::IntTypespec>();
                its->setSigned(false);
                its->setParent(pany);
                fC->populateCoreMembers(nodeId, nodeId, its);
                const std::string_view v = c->getValue();
                if (v.front() == '-') {
                  its->setSigned(true);
                }
                ts = its;
                p->setTypespec(ts);
                if (param->getTypespec() == nullptr) {
                  uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
                  tsRef->setParent(param);
                  param->setTypespec(tsRef);
                }
                param->getTypespec()->setActual(ts);
                break;
              }
              case vpiHexConst:
              case vpiOctConst:
              case vpiBinaryConst: {
                uhdm::IntTypespec* its = s.make<uhdm::IntTypespec>();
                its->setSigned(false);
                its->setParent(pany);
                fC->populateCoreMembers(nodeId, nodeId, its);
                if (c->getSize() != -1) {  // Unsized
                  uhdm::Range* r = s.make<uhdm::Range>();
                  uhdm::Constant* l = s.make<uhdm::Constant>();
                  l->setValue("INT:" + std::to_string(c->getSize() - 1));
                  l->setParent(r);
                  r->setLeftExpr(l);
                  fC->populateCoreMembers(name, name, l);

                  uhdm::Constant* rv = s.make<uhdm::Constant>();
                  rv->setValue(std::string("INT:0"));
                  rv->setParent(r);
                  fC->populateCoreMembers(value, value, rv);

                  r->setRightExpr(rv);
                  r->setParent(its);
                  fC->populateCoreMembers(Param_assignment, Param_assignment,
                                          r);
                  its->getRanges(true)->emplace_back(r);

                  ts = its;
                  p->setTypespec(ts);

                  if (param->getTypespec() == nullptr) {
                    uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
                    tsRef->setParent(param);
                    fC->populateCoreMembers(Data_type_or_implicit,
                                            Data_type_or_implicit, tsRef);
                    param->setTypespec(tsRef);
                  }
                  param->getTypespec()->setActual(ts);
                }
                break;
              }
              case vpiUIntConst: {
                uhdm::IntTypespec* its = s.make<uhdm::IntTypespec>();
                fC->populateCoreMembers(nodeId, nodeId, its);
                its->setParent(pany);
                its->setSigned(false);
                ts = its;
                p->setTypespec(ts);
                if (param->getTypespec() == nullptr) {
                  uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
                  tsRef->setParent(param);
                  fC->populateCoreMembers(Data_type_or_implicit,
                                          Data_type_or_implicit, tsRef);

                  param->setTypespec(tsRef);
                }
                param->getTypespec()->setActual(ts);
                break;
              }
              case vpiStringConst: {
                ts = s.make<uhdm::StringTypespec>();
                ts->setParent(pany);
                p->setTypespec(ts);
                if (param->getTypespec() == nullptr) {
                  uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
                  tsRef->setParent(param);
                  fC->populateCoreMembers(Data_type_or_implicit,
                                          Data_type_or_implicit, tsRef);
                  param->setTypespec(tsRef);
                }
                param->getTypespec()->setActual(ts);
                break;
              }
              default:
                break;
            }
          }
          if ((m_reduce == Reduce::Yes) && (reduce == Reduce::Yes))
            adjustSize(ts, component, compileDesign, instance, c);

          int32_t size = c->getSize();
          if (ts) {
            if (c->getTypespec() == nullptr) {
              uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
              tsRef->setParent(c);
              fC->populateCoreMembers(Data_type_or_implicit,
                                      Data_type_or_implicit, tsRef);
              c->setTypespec(tsRef);
            }
            c->getTypespec()->setActual(ts);

            if ((m_reduce == Reduce::Yes) && (reduce == Reduce::Yes)) {
              bool invalidValue = false;
              int32_t sizetmp = Bits(ts, invalidValue, component, compileDesign,
                                     Reduce::Yes, instance, fC->getFileId(),
                                     fC->Line(actual_value), false);
              if (!invalidValue) size = sizetmp;
            }
          }
          if (rhs->getTypespec() == nullptr) {
            uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
            tsRef->setParent(rhs);
            rhs->setTypespec(tsRef);
            fC->populateCoreMembers(Data_type_or_implicit,
                                    Data_type_or_implicit, tsRef);
            rhs->getTypespec()->setActual(ts);
          }
          c->setSize(size);
        }
        param_assign->setRhs(rhs);
        if (rhs) {
          rhs->setParent(param_assign);
          if (rhs->getUhdmType() == uhdm::UhdmType::Constant) {
            uhdm::Constant* c = (uhdm::Constant*)rhs;
            param->setValue(c->getValue());
          }
        }
      }
      Param_assignment = fC->Sibling(Param_assignment);
    }
  }

  compileDesign->unlockSerializer();
  return true;
}

char flip(char c) { return (c == '0') ? '1' : '0'; }

std::string twosComplement(std::string_view bin) {
  int32_t n = bin.length();
  int32_t i;
  std::string ones, twos;
  for (i = 0; i < n; i++) ones += flip(bin[i]);
  twos = ones;
  for (i = n - 1; i >= 0; i--) {
    if (ones[i] == '1')
      twos[i] = '0';
    else {
      twos[i] = '1';
      break;
    }
  }
  if (i == -1) twos = '1' + twos;
  return twos;
}

uhdm::Constant* CompileHelper::adjustSize(const uhdm::Typespec* ts,
                                          DesignComponent* component,
                                          CompileDesign* compileDesign,
                                          ValuedComponentI* instance,
                                          uhdm::Constant* c, bool uniquify,
                                          bool sizeMode) {
  uhdm::Serializer& s = compileDesign->getSerializer();
  uhdm::Constant* result = c;
  if (ts == nullptr) {
    return result;
  }
  FileSystem* const fileSystem = m_session->getFileSystem();
  SymbolTable* const symbols = m_session->getSymbolTable();
  int32_t orig_size = c->getSize();

  bool invalidValue = false;
  int32_t sizetmp = Bits(
      ts, invalidValue, component, compileDesign, Reduce::Yes, instance,
      fileSystem->toPathId(c->getFile(), symbols), c->getStartLine(), sizeMode);

  int32_t size = orig_size;
  if (c->getConstType() != vpiDecConst) {
    if (!invalidValue) size = sizetmp;
  }
  bool signedLhs = false;
  if (ts->getUhdmType() == uhdm::UhdmType::IntTypespec) {
    uhdm::IntTypespec* its = (uhdm::IntTypespec*)ts;
    signedLhs = its->getSigned();
  } else if (ts->getUhdmType() == uhdm::UhdmType::LogicTypespec) {
    uhdm::LogicTypespec* its = (uhdm::LogicTypespec*)ts;
    signedLhs = its->getSigned();
  } else if (ts->getUhdmType() == uhdm::UhdmType::BitTypespec) {
    uhdm::BitTypespec* its = (uhdm::BitTypespec*)ts;
    signedLhs = its->getSigned();
  }

  uhdm::ExprEval eval;
  int64_t val = eval.get_value(invalidValue, c);
  bool constantIsSigned = false;
  if (!invalidValue) {
    if (c->getConstType() == vpiUIntConst) {
      uint64_t mask = NumUtils::getMask(size);
      uint64_t uval = (uint64_t)val;
      uval = uval & mask;
      if (uniquify) {
        uhdm::ElaboratorContext elaboratorContext(&s, false, true);
        c = (uhdm::Constant*)uhdm::clone_tree(c, &elaboratorContext);
        result = c;
      }
      c->setValue("UINT:" + std::to_string(uval));
      c->setDecompile(std::to_string(uval));
      c->setConstType(vpiUIntConst);
      c->setSize(size);
    } else if (c->getConstType() == vpiBinaryConst) {
      if (const uhdm::RefTypespec* tstmp_rt = c->getTypespec()) {
        if (const uhdm::Typespec* tstmp = tstmp_rt->getActual()) {
          if (tstmp->getUhdmType() == uhdm::UhdmType::IntTypespec) {
            uhdm::IntTypespec* itps = (uhdm::IntTypespec*)tstmp;
            if (itps->getSigned()) {
              constantIsSigned = true;
            }
            if (!signedLhs) {
              itps->setSigned(false);
            }
          }
          ts = tstmp;
        }
      }
      if (ts) {
        uhdm::UhdmType ttype = ts->getUhdmType();
        if (ttype == uhdm::UhdmType::LogicTypespec) {
          std::string_view v = c->getValue();
          v.remove_prefix(4);
          if (orig_size > size) {
            if (v.size() > ((uint32_t)(orig_size - size)))
              v.remove_prefix(orig_size - size);
            c->setValue("BIN:" + std::string(v));
            c->setDecompile(v);
            c->setConstType(vpiBinaryConst);
            c->setSize(size);
          }
        } else if (ttype == uhdm::UhdmType::IntTypespec) {
          if (constantIsSigned) {
            uint64_t msb = val & 1 << (orig_size - 1);
            if (msb) {
              // 2's complement
              std::string v = std::string(c->getValue());
              v.erase(0, 4);
              if (signedLhs) {
                const std::string res = twosComplement(v);
                // Convert to int32_t
                val = std::strtoll(res.c_str(), nullptr, 2);
                val = -val;
              } else {
                if (size > orig_size) {
                  for (uint32_t i = 0; i < uint32_t(size - orig_size); i++) {
                    v += '1';
                  }
                  orig_size = size;
                }
                val = std::strtoll(v.c_str(), nullptr, 2);
              }
              if (uniquify) {
                uhdm::ElaboratorContext elaboratorContext(&s, false, true);
                c = (uhdm::Constant*)uhdm::clone_tree(c, &elaboratorContext);
                result = c;
              }
              c->setValue("INT:" + std::to_string(val));
              c->setDecompile(std::to_string(val));
              c->setConstType(vpiIntConst);
            } else if ((orig_size == 1) && (val == 1)) {
              uint64_t mask = NumUtils::getMask(size);
              if (uniquify) {
                uhdm::ElaboratorContext elaboratorContext(&s, false, true);
                c = (uhdm::Constant*)uhdm::clone_tree(c, &elaboratorContext);
                result = c;
              }
              c->setValue("UINT:" + std::to_string(mask));
              c->setDecompile(std::to_string(mask));
              c->setConstType(vpiUIntConst);
            }
          } else {
            if ((orig_size == -1) && (val == 1)) {
              uint64_t mask = NumUtils::getMask(size);
              if (uniquify) {
                uhdm::ElaboratorContext elaboratorContext(&s, false, true);
                c = (uhdm::Constant*)uhdm::clone_tree(c, &elaboratorContext);
                result = c;
              }
              c->setValue("UINT:" + std::to_string(mask));
              c->setDecompile(std::to_string(mask));
              c->setConstType(vpiUIntConst);
            }
          }
          c->setSize((orig_size < size) ? orig_size : size);
        }
      }
      if (orig_size == -1) {
        // '1, '0
        uint64_t uval = (uint64_t)val;
        if (uval == 1) {
          if (uniquify) {
            uhdm::ElaboratorContext elaboratorContext(&s, false, true);
            c = (uhdm::Constant*)uhdm::clone_tree(c, &elaboratorContext);
            result = c;
          }
          if (size <= 64) {
            uint64_t mask = NumUtils::getMask(size);
            uval = mask;
            c->setValue("UINT:" + std::to_string(uval));
            c->setDecompile(std::to_string(uval));
            c->setConstType(vpiUIntConst);
          } else {
            std::string mask(size, '1');
            c->setValue("BIN:" + mask);
            c->setDecompile(mask);
            c->setConstType(vpiBinaryConst);
          }
        }
        c->setSize(size);
      }
    } else {
      c->setSize(size);
    }
  }

  return result;
}

uhdm::Any* CompileHelper::compileTfCall(DesignComponent* component,
                                        const FileContent* fC,
                                        NodeId Tf_call_stmt,
                                        CompileDesign* compileDesign,
                                        uhdm::Any* pexpr) {
  uhdm::Serializer& s = compileDesign->getSerializer();
  CommandLineParser* const clp = m_session->getCommandLineParser();

  NodeId dollar_or_string = fC->Child(Tf_call_stmt);
  VObjectType leaf_type = fC->Type(dollar_or_string);
  NodeId tfNameNode;
  uhdm::TFCall* call = nullptr;
  std::string name;
  if (leaf_type == VObjectType::paDollar_keyword) {
    // System call, AST is:
    // n<> u<28> t<Subroutine_call> p<29> c<17> l<3>
    //     n<> u<17> t<Dollar_keyword> p<28> s<18> l<3>
    //     n<display> u<18> t<StringConst> p<28> s<27> l<3>
    //     n<> u<27> t<List_of_arguments> p<28> c<22> l<3>

    tfNameNode = fC->Sibling(dollar_or_string);
    call = s.make<uhdm::SysFuncCall>();
    name.assign("$").append(fC->SymName(tfNameNode));
  } else if (leaf_type == VObjectType::paImplicit_class_handle) {
    return compileComplexFuncCall(component, fC, fC->Child(Tf_call_stmt),
                                  compileDesign, Reduce::No, pexpr, nullptr,
                                  false);
  } else if (leaf_type == VObjectType::paDollar_root_keyword) {
    NodeId Dollar_root_keyword = dollar_or_string;
    NodeId nameId = fC->Sibling(Dollar_root_keyword);
    name.assign("$root.").append(fC->SymName(nameId));
    nameId = fC->Sibling(nameId);
    tfNameNode = nameId;
    uhdm::FuncCall* fcall = s.make<uhdm::FuncCall>();
    while (nameId) {
      if (fC->Type(nameId) == VObjectType::slStringConst) {
        name.append(".").append(fC->SymName(nameId));
        tfNameNode = nameId;
      } else if (fC->Type(nameId) == VObjectType::paConstant_bit_select) {
        NodeId Constant_expresion = fC->Child(nameId);
        if (Constant_expresion) {
          if (uhdm::Expr* select = (uhdm::Expr*)compileExpression(
                  component, fC, Constant_expresion, compileDesign, Reduce::No,
                  fcall)) {
            name.append("[").append(decompileHelper(select)).append("]");
          }
          tfNameNode = nameId;
        }
      } else {
        break;
      }
      nameId = fC->Sibling(nameId);
    }
    fcall->setName(name);
    fcall->setParent(pexpr);
    call = fcall;
  } else if (leaf_type == VObjectType::paSystem_task_names) {
    tfNameNode = dollar_or_string;
    call = s.make<uhdm::SysFuncCall>();
    name = fC->SymName(fC->Child(dollar_or_string));
  } else if (leaf_type == VObjectType::paImplicit_class_handle) {
    NodeId handle = fC->Child(dollar_or_string);
    if (fC->Type(handle) == VObjectType::paSuper_keyword ||
        fC->Type(handle) == VObjectType::paThis_keyword ||
        fC->Type(handle) == VObjectType::paThis_dot_super) {
      return (uhdm::TFCall*)compileComplexFuncCall(
          component, fC, fC->Child(Tf_call_stmt), compileDesign, Reduce::No,
          pexpr, nullptr, false);
    } else if (fC->Type(handle) == VObjectType::paDollar_root_keyword) {
      name = "$root.";
      tfNameNode = fC->Sibling(dollar_or_string);
      call = s.make<uhdm::SysFuncCall>();
      name += fC->SymName(tfNameNode);
    }
  } else if (leaf_type == VObjectType::paClass_scope) {
    return (uhdm::TFCall*)compileComplexFuncCall(
        component, fC, fC->Child(Tf_call_stmt), compileDesign, Reduce::No,
        pexpr, nullptr, false);
  } else {
    // User call, AST is:
    // n<> u<27> t<Subroutine_call> p<28> c<17> l<3>
    //     n<show> u<17> t<StringConst> p<27> s<26> l<3>
    //     n<> u<26> t<List_of_arguments> p<27> c<21> l<3>

    tfNameNode = dollar_or_string;
    name = fC->SymName(tfNameNode);
    NodeId Constant_bit_select = fC->Sibling(tfNameNode);
    while (fC->Type(Constant_bit_select) == VObjectType::paAttribute_instance) {
      Constant_bit_select = fC->Sibling(Constant_bit_select);
    }
    if (fC->Type(Constant_bit_select) == VObjectType::paConstant_bit_select) {
      tfNameNode = fC->Sibling(Constant_bit_select);
      uhdm::MethodFuncCall* fcall = s.make<uhdm::MethodFuncCall>();
      const std::string_view mname = fC->SymName(tfNameNode);
      NodeId argListNode = fC->Sibling(tfNameNode);
      fC->populateCoreMembers(dollar_or_string,
                              argListNode ? argListNode : tfNameNode, fcall);
      fcall->setName(mname);
      fcall->setParent(pexpr);
      uhdm::RefObj* prefix = s.make<uhdm::RefObj>();
      prefix->setName(name);
      prefix->setParent(fcall);
      fC->populateCoreMembers(dollar_or_string, dollar_or_string, prefix);
      fcall->setPrefix(prefix);
      call = fcall;
    }
    std::pair<uhdm::TaskFunc*, DesignComponent*> ret =
        getTaskFunc(name, component, compileDesign, nullptr, nullptr);
    uhdm::TaskFunc* tf = ret.first;
    if (tf) {
      if (tf->getUhdmType() == uhdm::UhdmType::Function) {
        uhdm::FuncCall* fcall = s.make<uhdm::FuncCall>();
        fcall->setFunction(any_cast<uhdm::Function>(tf));
        call = fcall;
      } else {
        uhdm::TaskCall* tcall = s.make<uhdm::TaskCall>();
        tcall->setTask(any_cast<uhdm::Task>(tf));
        call = tcall;
      }
      call->setParent(pexpr);
    }
    if (call == nullptr) {
      if (LetStmt* stmt = component->getLetStmt(name)) {
        if (clp->getLetExprSubstitution()) {
          // Inline the let declaration
          NodeId argListNode = fC->Sibling(tfNameNode);
          uhdm::AnyCollection* arguments =
              compileTfCallArguments(component, fC, argListNode, compileDesign,
                                     Reduce::No, call, nullptr, false);
          uhdm::Module* modTmp = s.make<uhdm::Module>();
          modTmp->setName("tmp");
          const uhdm::SeqFormalDeclCollection* decls = stmt->getIos();
          uhdm::ParamAssignCollection* passigns = modTmp->getParamAssigns(true);
          for (uint32_t i = 0; i < decls->size(); i++) {
            uhdm::SeqFormalDecl* decl = decls->at(i);
            uhdm::Any* actual = nullptr;
            if (i < arguments->size()) actual = arguments->at(i);
            uhdm::Parameter* p = s.make<uhdm::Parameter>();
            p->setName(decl->getName());
            uhdm::ParamAssign* pass = s.make<uhdm::ParamAssign>();
            pass->setLhs(p);
            if (actual) pass->setRhs(actual);
            passigns->emplace_back(pass);
          }
          uhdm::ContAssign* cts = s.make<uhdm::ContAssign>();
          uhdm::ContAssignCollection* assigns = modTmp->getContAssigns(true);
          const uhdm::Expr* exp = stmt->getExpr();
          cts->setRhs((uhdm::Expr*)exp);
          assigns->emplace_back(cts);

          if (uhdm::ElaboratorContext* elaboratorContext =
                  new uhdm::ElaboratorContext(&s, false)) {
            vpiHandle defModule = NewVpiHandle(modTmp);
            elaboratorContext->m_elaborator.listenModule(defModule);
            vpi_free_object(defModule);
            delete elaboratorContext;
          }
          return (uhdm::Any*)cts->getRhs();
        } else {
          uhdm::LetExpr* let = s.make<uhdm::LetExpr>();
          let->setParent(pexpr);
          let->setLetDecl((uhdm::LetDecl*)stmt->getDecl());
          NodeId argListNode = fC->Sibling(tfNameNode);
          if (uhdm::AnyCollection* arguments = compileTfCallArguments(
                  component, fC, argListNode, compileDesign, Reduce::No, let,
                  nullptr, false)) {
            uhdm::ExprCollection* exprs = let->getArguments(true);
            for (auto ex : *arguments) {
              exprs->emplace_back((uhdm::Expr*)ex);
            }
          }
          return let;
        }
      }
    }

    if (call == nullptr) {
      call = s.make<uhdm::FuncCall>();
      call->setParent(pexpr);
    }
  }
  if (call->getName().empty()) call->setName(name);
  if (call->getStartLine() == 0) {
    fC->populateCoreMembers(Tf_call_stmt, Tf_call_stmt, call);
  }
  NodeId argListNode = fC->Sibling(tfNameNode);
  while (fC->Type(argListNode) == VObjectType::paAttribute_instance) {
    argListNode = fC->Sibling(argListNode);
  }

  if (uhdm::AnyCollection* arguments =
          compileTfCallArguments(component, fC, argListNode, compileDesign,
                                 Reduce::No, call, nullptr, false)) {
    call->setArguments(arguments);
  }

  return call;
}

uhdm::AnyCollection* CompileHelper::compileTfCallArguments(
    DesignComponent* component, const FileContent* fC, NodeId Arg_list_node,
    CompileDesign* compileDesign, Reduce reduce, uhdm::Any* call,
    ValuedComponentI* instance, bool muteErrors) {
  uhdm::Serializer& s = compileDesign->getSerializer();
  if (fC->Type(Arg_list_node) == VObjectType::paSelect) {
    // Task or func call with no argument, not even ()
    return nullptr;
  }
  NodeId argumentNode = fC->Child(Arg_list_node);
  if (!argumentNode) return nullptr;
  uhdm::IODeclCollection* io_decls = nullptr;
  if (const uhdm::FuncCall* tf = any_cast<uhdm::FuncCall>(call)) {
    const uhdm::Function* func = tf->getFunction();
    if (func) io_decls = func->getIODecls();
  } else if (const uhdm::TaskCall* tf = any_cast<uhdm::TaskCall>(call)) {
    const uhdm::Task* task = tf->getTask();
    if (task) io_decls = task->getIODecls();
  }
  uhdm::AnyCollection* arguments = s.makeCollection<uhdm::Any>();
  std::map<std::string, uhdm::Any*, std::less<>> args;
  std::vector<uhdm::Any*> argOrder;
  while (argumentNode) {
    NodeId argument = argumentNode;
    if (fC->Type(argument) == VObjectType::paArgument) {
      argument = fC->Child(argument);
    }
    NodeId sibling = fC->Sibling(argument);
    NodeId Expression;
    if ((fC->Type(argument) == VObjectType::slStringConst) &&
        (fC->Type(sibling) == VObjectType::paExpression)) {
      // arg by name
      Expression = sibling;
      uhdm::Any* exp =
          compileExpression(component, fC, Expression, compileDesign, reduce,
                            call, instance, muteErrors);
      if (exp) {
        if (exp->getParent() == nullptr) exp->setParent(call);
        args.emplace(fC->SymName(argument), exp);
        argOrder.emplace_back(exp);
      }
      argumentNode = fC->Sibling(argumentNode);
    } else if (((fC->Type(argument) == VObjectType::paUnary_Tilda) ||
                (fC->Type(argument) == VObjectType::paUnary_Not)) &&
               (fC->Type(sibling) == VObjectType::paExpression)) {
      // arg by position
      Expression = argument;
      uhdm::Any* exp =
          compileExpression(component, fC, Expression, compileDesign, reduce,
                            call, instance, muteErrors);
      if (exp) {
        if (exp->getParent() == nullptr) exp->setParent(call);
        arguments->emplace_back(exp);
      }
      argumentNode = fC->Sibling(argumentNode);
    } else {
      // arg by position
      Expression = argument;
      if (Expression) {
        if (uhdm::Any* exp =
                compileExpression(component, fC, Expression, compileDesign,
                                  reduce, call, instance, muteErrors)) {
          arguments->emplace_back(exp);
          exp->setParent(call);
        }
      } else {
        uhdm::Constant* c = s.make<uhdm::Constant>();
        c->setValue("INT:0");
        c->setDecompile("0");
        c->setSize(64);
        c->setConstType(vpiIntConst);
        c->setParent(call);
        fC->populateCoreMembers(argumentNode, argumentNode, c);
        arguments->emplace_back(c);
      }
    }
    argumentNode = fC->Sibling(argumentNode);
  }
  if (NodeId clocking = fC->Sibling(Arg_list_node)) {
    if (fC->Type(clocking) == VObjectType::paClocking_event) {
      if (uhdm::Any* exp =
              compileExpression(component, fC, clocking, compileDesign, reduce,
                                call, instance, muteErrors)) {
        arguments->emplace_back(exp);
        exp->setParent(call);
      }
    }
  }
  if (!args.empty()) {
    if (io_decls) {
      for (uhdm::IODecl* decl : *io_decls) {
        const std::string_view name = decl->getName();
        std::map<std::string, uhdm::Any*>::iterator itr = args.find(name);
        if (itr != args.end()) {
          arguments->emplace_back((*itr).second);
        } else if (m_elaborate == Elaborate::Yes) {
          if (const uhdm::Constant* const def =
                  decl->getExpr<uhdm::Constant>()) {
            uhdm::Constant* c = s.make<uhdm::Constant>();
            c->setValue(def->getValue());
            c->setDecompile(def->getDecompile());
            c->setSize(def->getSize());
            c->setConstType(def->getConstType());
            c->setParent(call);
            fC->populateCoreMembers(InvalidNodeId, InvalidNodeId, c);
            arguments->emplace_back(c);
          }
        }
      }
    } else {
      for (uhdm::Any* exp : argOrder) {
        arguments->emplace_back(exp);
      }
    }
  }

  return arguments;
}

uhdm::Assignment* CompileHelper::compileBlockingAssignment(
    DesignComponent* component, const FileContent* fC,
    NodeId Operator_assignment, bool blocking, CompileDesign* compileDesign,
    uhdm::Any* pstmt, ValuedComponentI* instance) {
  uhdm::Serializer& s = compileDesign->getSerializer();
  NodeId Variable_lvalue;
  if (fC->Type(Operator_assignment) == VObjectType::paVariable_lvalue) {
    Variable_lvalue = Operator_assignment;
  } else if (fC->Type(Operator_assignment) == VObjectType::slStringConst) {
    Variable_lvalue = Operator_assignment;
  } else {
    Variable_lvalue = fC->Child(Operator_assignment);
  }
  uhdm::Assignment* assign = s.make<uhdm::Assignment>();
  uhdm::Expr* lhs_rf = nullptr;
  uhdm::Any* rhs_rf = nullptr;
  NodeId Delay_or_event_control;
  NodeId AssignOp_Assign;
  if (fC->Type(Variable_lvalue) == VObjectType::paHierarchical_identifier ||
      fC->Type(Variable_lvalue) == VObjectType::slStringConst) {
    NodeId Variable_lvalue = Operator_assignment;
    Delay_or_event_control = fC->Sibling(Variable_lvalue);
    NodeId Expression = fC->Sibling(Delay_or_event_control);
    lhs_rf = any_cast<uhdm::Expr>(
        compileExpression(component, fC, Variable_lvalue, compileDesign,
                          Reduce::No, assign, instance));
    AssignOp_Assign = InvalidNodeId;
    if (fC->Type(Delay_or_event_control) == VObjectType::paDynamic_array_new) {
      uhdm::MethodFuncCall* fcall = s.make<uhdm::MethodFuncCall>();
      fcall->setParent(assign);
      fC->populateCoreMembers(Delay_or_event_control, Delay_or_event_control,
                              fcall);
      fcall->setName("new");
      NodeId List_of_arguments = fC->Child(Delay_or_event_control);
      if (List_of_arguments) {
        if (uhdm::AnyCollection* arguments = compileTfCallArguments(
                component, fC, Delay_or_event_control, compileDesign,
                Reduce::No, fcall, nullptr, false)) {
          fcall->setArguments(arguments);
        }
      }
      Delay_or_event_control = InvalidNodeId;
      rhs_rf = fcall;
    } else {
      rhs_rf = compileExpression(component, fC, Expression, compileDesign,
                                 Reduce::No, assign, instance);
    }
  } else if (fC->Type(Variable_lvalue) == VObjectType::paVariable_lvalue) {
    AssignOp_Assign = fC->Sibling(Variable_lvalue);
    NodeId Hierarchical_identifier = fC->Child(Variable_lvalue);
    if (fC->Type(fC->Child(Hierarchical_identifier)) ==
        VObjectType::paHierarchical_identifier) {
      Hierarchical_identifier = fC->Child(Hierarchical_identifier);
      Hierarchical_identifier = fC->Child(Hierarchical_identifier);
    } else if (fC->Type(Hierarchical_identifier) !=
               VObjectType::paPs_or_hierarchical_identifier) {
      Hierarchical_identifier = Variable_lvalue;
    }

    lhs_rf = any_cast<uhdm::Expr>(
        compileExpression(component, fC, Hierarchical_identifier, compileDesign,
                          Reduce::No, assign, instance));
    NodeId Expression;
    if (fC->Type(AssignOp_Assign) == VObjectType::paExpression) {
      Expression = AssignOp_Assign;
      AssignOp_Assign = InvalidNodeId;
    } else if (fC->Type(AssignOp_Assign) ==
               VObjectType::paDelay_or_event_control) {
      Delay_or_event_control = AssignOp_Assign;
      Expression = fC->Sibling(AssignOp_Assign);
      AssignOp_Assign = InvalidNodeId;
    } else {
      Expression = fC->Sibling(AssignOp_Assign);
    }
    rhs_rf = compileExpression(component, fC, Expression, compileDesign,
                               Reduce::No, assign, instance);
  } else if (fC->Type(Operator_assignment) ==
             VObjectType::paHierarchical_identifier) {
    //  = new ...
    NodeId Hierarchical_identifier = Operator_assignment;
    NodeId Select = fC->Sibling(Hierarchical_identifier);
    NodeId Class_new = fC->Sibling(Select);
    NodeId List_of_arguments = fC->Child(Class_new);
    lhs_rf = any_cast<uhdm::Expr>(
        compileExpression(component, fC, Hierarchical_identifier, compileDesign,
                          Reduce::No, assign, instance));
    uhdm::MethodFuncCall* fcall = s.make<uhdm::MethodFuncCall>();
    fcall->setName("new");
    fcall->setParent(assign);
    fC->populateCoreMembers(Hierarchical_identifier, Hierarchical_identifier,
                            fcall);
    if (List_of_arguments) {
      if (uhdm::AnyCollection* arguments = compileTfCallArguments(
              component, fC, List_of_arguments, compileDesign, Reduce::No,
              fcall, nullptr, false)) {
        fcall->setArguments(arguments);
      }
    }

    rhs_rf = fcall;
  }

  if (Delay_or_event_control &&
      (fC->Type(Delay_or_event_control) != VObjectType::paSelect)) {
    uhdm::DelayControl* delay_control = s.make<uhdm::DelayControl>();
    assign->setDelayControl(delay_control);
    delay_control->setParent(assign);
    NodeId Delay_control = fC->Child(Delay_or_event_control);
    NodeId IntConst = fC->Child(Delay_control);
    const std::string_view value = fC->SymName(IntConst);
    delay_control->setVpiDelay(value);
    fC->populateCoreMembers(fC->Child(Delay_control), fC->Child(Delay_control),
                            delay_control);
  }
  if (AssignOp_Assign)
    assign->setOpType(UhdmWriter::getVpiOpType(fC->Type(AssignOp_Assign)));
  else
    assign->setOpType(vpiAssignmentOp);
  if (blocking) assign->setBlocking(true);
  assign->setLhs(lhs_rf);
  assign->setRhs(rhs_rf);
  return assign;
}

uhdm::ArrayVar* CompileHelper::compileArrayVar(DesignComponent* component,
                                               const FileContent* fC,
                                               NodeId varId,
                                               CompileDesign* compileDesign,
                                               uhdm::Any* pexpr,
                                               ValuedComponentI* instance) {
  uhdm::Serializer& s = compileDesign->getSerializer();
  uhdm::ArrayVar* result = s.make<uhdm::ArrayVar>();

  return result;
}

uhdm::AttributeCollection* CompileHelper::compileAttributes(
    DesignComponent* component, const FileContent* fC, NodeId nodeId,
    CompileDesign* compileDesign, uhdm::Any* pexpr) {
  // NOTE(HS): pexpr is expected to be null here sometimes
  // e.g. Attributes2
  uhdm::Serializer& s = compileDesign->getSerializer();
  std::vector<uhdm::Attribute*>* results = nullptr;
  if (fC->Type(nodeId) == VObjectType::paAttribute_instance) {
    results = s.makeCollection<uhdm::Attribute>();
    while (fC->Type(nodeId) == VObjectType::paAttribute_instance) {
      uhdm::Attribute* attribute = s.make<uhdm::Attribute>();
      NodeId Attr_spec = fC->Child(nodeId);
      NodeId Attr_name = fC->Child(Attr_spec);
      const std::string_view name = fC->SymName(fC->Child(Attr_name));
      attribute->setName(name);
      attribute->setParent(pexpr);
      fC->populateCoreMembers(Attr_spec, Attr_spec, attribute);
      results->emplace_back(attribute);
      if (NodeId Constant_expression = fC->Sibling(Attr_name)) {
        if (uhdm::Expr* expr = (uhdm::Expr*)compileExpression(
                component, fC, Constant_expression, compileDesign, Reduce::No,
                attribute)) {
          attribute->setValue(expr->getValue());
        }
      }
      nodeId = fC->Sibling(nodeId);
    }
  }
  return results;
}

uhdm::ClockingBlock* CompileHelper::compileClockingBlock(
    DesignComponent* component, const FileContent* fC, NodeId nodeId,
    CompileDesign* compileDesign, uhdm::Any* pstmt,
    ValuedComponentI* instance) {
  uhdm::Serializer& s = compileDesign->getSerializer();
  uhdm::ClockingBlock* cblock = s.make<uhdm::ClockingBlock>();

  NodeId clocking_block_type = fC->Child(nodeId);
  NodeId clocking_block_name;
  std::string name;
  if (fC->Type(clocking_block_type) == VObjectType::paDEFAULT) {
  } else if (fC->Type(clocking_block_type) == VObjectType::paGLOBAL) {
  } else if (fC->Type(clocking_block_type) == VObjectType::slStringConst) {
    clocking_block_name = clocking_block_type;
  }
  NodeId clocking_event = fC->Sibling(clocking_block_type);
  if (fC->Type(clocking_event) == VObjectType::slStringConst) {
    clocking_block_name = clocking_event;
    clocking_event = fC->Sibling(clocking_block_name);
  }
  if (clocking_block_name)
    name = fC->SymName(clocking_block_name);
  else
    name = "unnamed_clocking_block";
  cblock->setName(name);
  fC->populateCoreMembers(nodeId, nodeId, cblock);
  uhdm::EventControl* ctrl = compileClocking_event(
      component, fC, clocking_event, compileDesign, cblock, instance);
  cblock->setClockingEvent(ctrl);
  NodeId clocking_item = fC->Sibling(clocking_event);
  while (clocking_item) {
    if (fC->Type(clocking_item) == VObjectType::paClocking_item) {
      NodeId item = fC->Child(clocking_item);
      VObjectType direction = fC->Type(item);
      uhdm::DelayControl* dcInp = nullptr;
      uhdm::DelayControl* dcOut = nullptr;
      int32_t inputEdge = 0;
      int32_t outputEdge = 0;
      if (direction == VObjectType::paDefaultSkew_IntputOutput) {
        NodeId Clocking_skew = fC->Child(item);
        if (Clocking_skew) {
          NodeId Edge = fC->Child(Clocking_skew);
          NodeId Skew = Clocking_skew;
          if (fC->Type(Edge) == VObjectType::paEdge_Negedge) {
            cblock->setInputEdge(vpiNegedge);
            Skew = fC->Sibling(Edge);
          } else if (fC->Type(Edge) == VObjectType::paEdge_Posedge) {
            cblock->setInputEdge(vpiPosedge);
            Skew = fC->Sibling(Edge);
          } else if (fC->Type(Edge) == VObjectType::paEdge_Edge) {
            cblock->setInputEdge(vpiAnyEdge);
            Skew = fC->Sibling(Edge);
          }
          if (Skew) {
            uhdm::DelayControl* dc = (uhdm::DelayControl*)compileDelayControl(
                component, fC, Skew, compileDesign, cblock, instance);
            cblock->setInputSkew(dc);
          }
          Clocking_skew = fC->Sibling(Clocking_skew);
          if (Clocking_skew) {
            NodeId Edge = fC->Child(Clocking_skew);
            NodeId Skew = Clocking_skew;
            if (fC->Type(Edge) == VObjectType::paEdge_Negedge) {
              cblock->setOutputEdge(vpiNegedge);
              Skew = fC->Sibling(Edge);
            } else if (fC->Type(Edge) == VObjectType::paEdge_Posedge) {
              cblock->setOutputEdge(vpiPosedge);
              Skew = fC->Sibling(Edge);
            } else if (fC->Type(Edge) == VObjectType::paEdge_Edge) {
              cblock->setOutputEdge(vpiAnyEdge);
              Skew = fC->Sibling(Edge);
            }
            if (Skew) {
              uhdm::DelayControl* dc = (uhdm::DelayControl*)compileDelayControl(
                  component, fC, Clocking_skew, compileDesign, cblock,
                  instance);
              cblock->setOutputSkew(dc);
            }
          }
        }
      }
      if (direction == VObjectType::paDefaultSkew_Intput) {
        NodeId Clocking_skew = fC->Child(item);
        if (Clocking_skew) {
          NodeId Edge = fC->Child(Clocking_skew);
          NodeId Skew = Clocking_skew;
          if (fC->Type(Edge) == VObjectType::paEdge_Negedge) {
            cblock->setInputEdge(vpiNegedge);
            Skew = fC->Sibling(Edge);
          } else if (fC->Type(Edge) == VObjectType::paEdge_Posedge) {
            cblock->setInputEdge(vpiPosedge);
            Skew = fC->Sibling(Edge);
          } else if (fC->Type(Edge) == VObjectType::paEdge_Edge) {
            cblock->setInputEdge(vpiAnyEdge);
            Skew = fC->Sibling(Edge);
          }
          if (Skew) {
            uhdm::DelayControl* dc = (uhdm::DelayControl*)compileDelayControl(
                component, fC, Skew, compileDesign, cblock, instance);
            cblock->setInputSkew(dc);
          }
        }
      }
      if (direction == VObjectType::paDefaultSkew_Output) {
        NodeId Clocking_skew = fC->Child(item);
        if (Clocking_skew) {
          NodeId Edge = fC->Child(Clocking_skew);
          NodeId Skew = Clocking_skew;
          if (fC->Type(Edge) == VObjectType::paEdge_Negedge) {
            cblock->setOutputEdge(vpiNegedge);
            Skew = fC->Sibling(Edge);
          } else if (fC->Type(Edge) == VObjectType::paEdge_Posedge) {
            cblock->setOutputEdge(vpiPosedge);
            Skew = fC->Sibling(Edge);
          } else if (fC->Type(Edge) == VObjectType::paEdge_Edge) {
            cblock->setOutputEdge(vpiAnyEdge);
            Skew = fC->Sibling(Edge);
          }
          if (Skew) {
            uhdm::DelayControl* dc = (uhdm::DelayControl*)compileDelayControl(
                component, fC, Skew, compileDesign, cblock, instance);
            cblock->setOutputSkew(dc);
          }
        }
      } else if (direction == VObjectType::paClockingDir_Input) {
        NodeId Clocking_skew = fC->Child(item);
        if (Clocking_skew) {
          NodeId Edge = fC->Child(Clocking_skew);
          NodeId Skew = Clocking_skew;
          if (fC->Type(Edge) == VObjectType::paEdge_Negedge) {
            inputEdge = vpiNegedge;
            Skew = fC->Sibling(Edge);
          } else if (fC->Type(Edge) == VObjectType::paEdge_Posedge) {
            inputEdge = vpiPosedge;
            Skew = fC->Sibling(Edge);
          } else if (fC->Type(Edge) == VObjectType::paEdge_Edge) {
            inputEdge = vpiAnyEdge;
            Skew = fC->Sibling(Edge);
          }
          if (Skew) {
            dcInp = (uhdm::DelayControl*)compileDelayControl(
                component, fC, Skew, compileDesign, cblock, instance);
          }
        }
      } else if (direction == VObjectType::paClockingDir_Output) {
        NodeId Clocking_skew = fC->Child(item);
        if (Clocking_skew) {
          NodeId Edge = fC->Child(Clocking_skew);
          NodeId Skew = Clocking_skew;
          if (fC->Type(Edge) == VObjectType::paEdge_Negedge) {
            outputEdge = vpiNegedge;
            Skew = fC->Sibling(Edge);
          } else if (fC->Type(Edge) == VObjectType::paEdge_Posedge) {
            outputEdge = vpiPosedge;
            Skew = fC->Sibling(Edge);
          } else if (fC->Type(Edge) == VObjectType::paEdge_Edge) {
            outputEdge = vpiAnyEdge;
            Skew = fC->Sibling(Edge);
          }
          if (Skew) {
            dcOut = (uhdm::DelayControl*)compileDelayControl(
                component, fC, Skew, compileDesign, cblock, instance);
          }
        }
      } else if (direction == VObjectType::paClockingDir_InputOutput) {
        NodeId Clocking_skew = fC->Child(item);
        if (Clocking_skew) {
          NodeId Edge = fC->Child(Clocking_skew);
          NodeId Skew = Clocking_skew;
          if (fC->Type(Edge) == VObjectType::paEdge_Negedge) {
            inputEdge = vpiNegedge;
            Skew = fC->Sibling(Edge);
          } else if (fC->Type(Edge) == VObjectType::paEdge_Posedge) {
            inputEdge = vpiPosedge;
            Skew = fC->Sibling(Edge);
          } else if (fC->Type(Edge) == VObjectType::paEdge_Edge) {
            inputEdge = vpiAnyEdge;
            Skew = fC->Sibling(Edge);
          }
          if (Skew) {
            dcInp = (uhdm::DelayControl*)compileDelayControl(
                component, fC, Skew, compileDesign, cblock, instance);
          }

          Clocking_skew = fC->Sibling(Clocking_skew);
          if (Clocking_skew) {
            NodeId Edge = fC->Child(Clocking_skew);
            NodeId Skew = Clocking_skew;
            if (fC->Type(Edge) == VObjectType::paEdge_Negedge) {
              outputEdge = vpiNegedge;
              Skew = fC->Sibling(Edge);
            } else if (fC->Type(Edge) == VObjectType::paEdge_Posedge) {
              outputEdge = vpiPosedge;
              Skew = fC->Sibling(Edge);
            } else if (fC->Type(Edge) == VObjectType::paEdge_Edge) {
              outputEdge = vpiAnyEdge;
              Skew = fC->Sibling(Edge);
            }
            if (Skew) {
              dcOut = (uhdm::DelayControl*)compileDelayControl(
                  component, fC, Skew, compileDesign, cblock, instance);
            }
          }
        }
      } else if (direction == VObjectType::paClockingDir_Inout) {
        // No skew value
      }

      NodeId List_of_clocking_decl_assign = fC->Sibling(item);
      if (List_of_clocking_decl_assign) {
        NodeId Clocking_decl_assign = fC->Child(List_of_clocking_decl_assign);
        uhdm::ClockingIODeclCollection* ios = cblock->getClockingIODecls(true);
        while (Clocking_decl_assign) {
          NodeId Identifier = fC->Child(Clocking_decl_assign);
          NodeId Expr = fC->Sibling(Identifier);
          uhdm::ClockingIODecl* io = s.make<uhdm::ClockingIODecl>();
          io->setInputEdge(inputEdge);
          io->setOutputEdge(outputEdge);
          io->setParent(cblock);
          fC->populateCoreMembers(Clocking_decl_assign, Clocking_decl_assign,
                                  io);
          if (Expr) {
            if (uhdm::Expr* exp = (uhdm::Expr*)compileExpression(
                    component, fC, Expr, compileDesign, Reduce::No, io,
                    instance)) {
              io->setExpr(exp);
            }
          }
          ios->emplace_back(io);
          const std::string_view sigName = fC->SymName(Identifier);
          io->setName(sigName);
          if (direction == VObjectType::paClockingDir_Input) {
            io->setInputSkew(dcInp);
            io->setDirection(vpiInput);
          } else if (direction == VObjectType::paClockingDir_Output) {
            io->setOutputSkew(dcOut);
            io->setDirection(vpiOutput);
          } else if (direction == VObjectType::paClockingDir_InputOutput) {
            io->setInputSkew(dcInp);
            io->setOutputSkew(dcOut);
            io->setDirection(vpiOutput);
          } else if (direction == VObjectType::paClockingDir_Inout) {
            io->setDirection(vpiInout);
          }
          Clocking_decl_assign = fC->Sibling(Clocking_decl_assign);
        }
      }
    }
    clocking_item = fC->Sibling(clocking_item);
  }
  return cblock;
}

uhdm::EventControl* CompileHelper::compileClocking_event(
    DesignComponent* component, const FileContent* fC, NodeId nodeId,
    CompileDesign* compileDesign, uhdm::Any* pexpr,
    ValuedComponentI* instance) {
  uhdm::Serializer& s = compileDesign->getSerializer();
  uhdm::EventControl* ctrl = s.make<uhdm::EventControl>();
  ctrl->setParent(pexpr);
  fC->populateCoreMembers(nodeId, nodeId, ctrl);
  NodeId identifier = fC->Child(nodeId);
  if (uhdm::Any* exp =
          compileExpression(component, fC, identifier, compileDesign,
                            Reduce::No, ctrl, instance)) {
    ctrl->setCondition(exp);
  }
  return ctrl;
}

bool CompileHelper::isSelected(const FileContent* fC,
                               NodeId ps_or_hierarchical_identifier) {
  NodeId Constant_select = fC->Sibling(ps_or_hierarchical_identifier);
  NodeId Constant_bit_select = fC->Child(Constant_select);
  NodeId Constant_expression = fC->Child(Constant_bit_select);
  NodeId Constant_part_select_range = fC->Sibling(Constant_bit_select);
  if (Constant_part_select_range) {
    return true;
  }
  if (Constant_expression) return true;
  return false;
}

void CompileHelper::adjustUnsized(uhdm::Constant* c, int32_t size) {
  if (c == nullptr) return;
  int32_t csize = c->getSize();
  if (csize == -1) {
    uhdm::ExprEval eval;
    bool invalidValue = false;
    uint64_t lv = eval.get_uvalue(invalidValue, c);
    if (lv == 1) {
      if (size <= 64) {
        uint64_t mask = NumUtils::getMask(size);
        c->setValue("UINT:" + std::to_string(mask));
        c->setDecompile(std::to_string(mask));
        c->setConstType(vpiUIntConst);
      } else {
        std::string mask(size, '1');
        c->setValue("BIN:" + mask);
        c->setDecompile(mask);
        c->setConstType(vpiBinaryConst);
      }
    }
  }
}

int32_t CompileHelper::adjustOpSize(const uhdm::Typespec* tps, uhdm::Expr* cop,
                                    int32_t opIndex, uhdm::Expr* rhs,
                                    DesignComponent* component,
                                    CompileDesign* compileDesign,
                                    ValuedComponentI* instance) {
  FileSystem* const fileSystem = m_session->getFileSystem();
  SymbolTable* const symbols = m_session->getSymbolTable();
  bool invalidValue = false;
  int32_t csize = cop->getSize();
  if (csize == 0) {
    uhdm::Expr* vexp =
        reduceExpr(cop, invalidValue, component, compileDesign, instance,
                   fileSystem->toPathId(cop->getFile(), symbols),
                   cop->getStartLine(), nullptr);
    if (invalidValue == false && vexp) csize = vexp->getSize();
  }

  const uhdm::Typespec* rtps = nullptr;
  if (const uhdm::RefTypespec* rt = rhs->getTypespec()) {
    rtps = rt->getActual();
  }
  if (rtps == nullptr) {
    rtps = tps;
  }
  if (rtps->getUhdmType() == uhdm::UhdmType::StructTypespec) {
    uhdm::StructTypespec* stps = (uhdm::StructTypespec*)rtps;
    int32_t index = 0;
    for (uhdm::TypespecMember* member : *stps->getMembers()) {
      if (index == opIndex) {
        const uhdm::Typespec* mtps = nullptr;
        if (const uhdm::RefTypespec* rt = member->getTypespec()) {
          mtps = rt->getActual();
        }
        int32_t ncsize =
            Bits(mtps, invalidValue, component, compileDesign, Reduce::Yes,
                 instance, fileSystem->toPathId(member->getFile(), symbols),
                 member->getStartLine(), false);
        // Fix the size of the member:
        adjustUnsized(any_cast<uhdm::Constant>(cop), ncsize);
        cop->setSize(ncsize);
        break;
      }
      index++;
    }
  } else if (rtps->getUhdmType() == uhdm::UhdmType::ArrayTypespec) {
    uhdm::ArrayTypespec* atps = (uhdm::ArrayTypespec*)rtps;
    if (const uhdm::RefTypespec* ert = atps->getElemTypespec()) {
      int32_t ncsize = Bits(ert->getActual(), invalidValue, component,
                            compileDesign, Reduce::Yes, instance,
                            fileSystem->toPathId(rtps->getFile(), symbols),
                            rtps->getStartLine(), false);
      // Fix the size of the member:
      adjustUnsized(any_cast<uhdm::Constant>(cop), ncsize);
      cop->setSize(ncsize);
    }
  } else if (rtps->getUhdmType() == uhdm::UhdmType::LogicTypespec) {
    uint64_t fullSize =
        Bits(rtps, invalidValue, component, compileDesign, Reduce::Yes,
             instance, fileSystem->toPathId(rtps->getFile(), symbols),
             rtps->getStartLine(), false);
    uint64_t innerSize =
        Bits(rtps, invalidValue, component, compileDesign, Reduce::Yes,
             instance, fileSystem->toPathId(rtps->getFile(), symbols),
             rtps->getStartLine(), true);
    int32_t ncsize = fullSize / innerSize;
    // Fix the size of the member:
    adjustUnsized(any_cast<uhdm::Constant>(cop), ncsize);
    cop->setSize(ncsize);
  } else {
    int32_t ncsize =
        Bits(rtps, invalidValue, component, compileDesign, Reduce::Yes,
             instance, fileSystem->toPathId(rtps->getFile(), symbols),
             rtps->getStartLine(), false);
    // Fix the size of the member:
    adjustUnsized(any_cast<uhdm::Constant>(cop), ncsize);
    cop->setSize(ncsize);
  }

  return cop->getSize();
}

uhdm::Expr* CompileHelper::expandPatternAssignment(
    const uhdm::Typespec* tps, uhdm::Expr* rhs, DesignComponent* component,
    CompileDesign* compileDesign, Reduce reduce, ValuedComponentI* instance) {
  FileSystem* const fileSystem = m_session->getFileSystem();
  SymbolTable* const symbolTable = m_session->getSymbolTable();
  uhdm::Serializer& s = compileDesign->getSerializer();

  uhdm::Expr* result = rhs;
  uhdm::AnyCollection* vars = nullptr;
  if (tps == nullptr) return result;
  if (tps->getUhdmType() == uhdm::UhdmType::PackedArrayTypespec ||
      tps->getUhdmType() == uhdm::UhdmType::LogicTypespec ||
      tps->getUhdmType() == uhdm::UhdmType::StructTypespec) {
    vars = s.makeCollection<uhdm::Any>();
  }

  bool invalidValue = false;
  uint64_t size =
      Bits(tps, invalidValue, component, compileDesign, Reduce::Yes, instance,
           fileSystem->toPathId(rhs->getFile(), symbolTable),
           rhs->getStartLine(), false);
  uint64_t patternSize = 0;

  uhdm::ExprEval eval(true);
  rhs = eval.flattenPatternAssignments(s, tps, rhs);

  std::vector<int32_t> values(size, 0);
  if (rhs->getUhdmType() == uhdm::UhdmType::Operation) {
    uhdm::Operation* op = (uhdm::Operation*)rhs;
    int32_t opType = op->getOpType();
    if (opType == vpiConditionOp) {
      uhdm::AnyCollection* ops = op->getOperands();
      ops->at(1) =
          expandPatternAssignment(tps, (uhdm::Expr*)ops->at(1), component,
                                  compileDesign, reduce, instance);
      ops->at(2) =
          expandPatternAssignment(tps, (uhdm::Expr*)ops->at(2), component,
                                  compileDesign, reduce, instance);
      return result;
    } else if (opType == vpiAssignmentPatternOp) {
      uhdm::AnyCollection* operands = op->getOperands();
      if (operands) {
        // Get default
        int32_t defaultval = 0;
        bool taggedPattern = false;
        for (uhdm::Any* op : *operands) {
          if (op->getUhdmType() == uhdm::UhdmType::TaggedPattern) {
            taggedPattern = true;
            uhdm::TaggedPattern* tp = (uhdm::TaggedPattern*)op;
            if (const uhdm::RefTypespec* rt = tp->getTypespec()) {
              if (const uhdm::Typespec* tpsi = rt->getActual()) {
                if ((m_reduce == Reduce::Yes) && (reduce == Reduce::Yes) &&
                    (tpsi->getName() == "default")) {
                  bool invalidValue = false;
                  uhdm::ExprEval eval;
                  defaultval = eval.get_value(
                      invalidValue,
                      reduceExpr((uhdm::Any*)tp->getPattern(), invalidValue,
                                 component, compileDesign, instance,
                                 fileSystem->toPathId(
                                     tp->getPattern()->getFile(), symbolTable),
                                 tp->getPattern()->getStartLine(), nullptr));

                  break;
                }
              }
            }
          }
        }
        if (taggedPattern) {
          const uhdm::Typespec* rtps = nullptr;
          if (const uhdm::RefTypespec* rt = rhs->getTypespec()) {
            rtps = rt->getActual();
          }
          if (rtps == nullptr) {
            rtps = tps;
          }
          if (rtps->getUhdmType() == uhdm::UhdmType::StructTypespec) {
            uhdm::StructTypespec* stps = (uhdm::StructTypespec*)rtps;
            int32_t valIndex = 0;
            // Apply default
            for (uhdm::TypespecMember* member : *stps->getMembers()) {
              uint64_t csize = Bits(
                  member, invalidValue, component, compileDesign, Reduce::Yes,
                  instance, fileSystem->toPathId(rhs->getFile(), symbolTable),
                  rhs->getStartLine(), false);
              patternSize += csize;
              if (invalidValue) {
                return result;
              }
              for (uint64_t i = 0; i < csize; i++) {
                if (valIndex > (int32_t)(size - 1)) {
                  break;
                }
                {
                  int shift = (csize - 1 - i);
                  if (shift < 0 || shift >= 64) {
                    return result;
                  }
                }
                values[valIndex] =
                    (defaultval & (1 << (csize - 1 - i))) ? 1 : 0;
                valIndex++;
              }
            }
            valIndex = 0;
            for (uhdm::TypespecMember* member : *stps->getMembers()) {
              uint64_t csize = Bits(
                  member, invalidValue, component, compileDesign, Reduce::Yes,
                  instance, fileSystem->toPathId(rhs->getFile(), symbolTable),
                  rhs->getStartLine(), false);

              for (uhdm::Any* op : *operands) {
                bool found = false;
                int32_t val = 0;
                if (op->getUhdmType() == uhdm::UhdmType::TaggedPattern) {
                  taggedPattern = true;
                  uhdm::TaggedPattern* tp = (uhdm::TaggedPattern*)op;
                  if (const uhdm::RefTypespec* rt = tp->getTypespec()) {
                    if (const uhdm::Typespec* tpsi = rt->getActual()) {
                      if (tpsi->getName() == member->getName()) {
                        bool invalidValue = false;
                        uhdm::ExprEval eval;
                        val = eval.get_value(
                            invalidValue,
                            reduceExpr(
                                (uhdm::Any*)tp->getPattern(), invalidValue,
                                component, compileDesign, instance,
                                fileSystem->toPathId(
                                    tp->getPattern()->getFile(), symbolTable),
                                tp->getPattern()->getStartLine(), nullptr));
                        found = true;
                        if (invalidValue) {
                          return result;
                        }
                      }
                    }
                  }
                }

                for (uint64_t i = 0; i < csize; i++) {
                  if (valIndex > (int32_t)(size - 1)) {
                    break;
                  }
                  {
                    int shift = (csize - 1 - i);
                    if (shift < 0 || shift >= 64) {
                      return result;
                    }
                  }
                  if (found) {
                    values[valIndex] = (val & (1 << (csize - 1 - i))) ? 1 : 0;
                  }
                  valIndex++;
                }
              }
            }
          } else if (rtps->getUhdmType() == uhdm::UhdmType::LogicTypespec) {
            // Apply default
            // parameter logic[7:0] P = '{default: 1};
            patternSize += size;
            for (uint64_t i = 0; i < size; i++) {
              values[i] = defaultval;
            }
            // Apply any other indexed value
            for (uhdm::Any* op : *operands) {
              if (op->getUhdmType() == uhdm::UhdmType::TaggedPattern) {
                taggedPattern = true;
                uhdm::TaggedPattern* tp = (uhdm::TaggedPattern*)op;
                if (const uhdm::RefTypespec* rt = tp->getTypespec()) {
                  if (const uhdm::Typespec* tpsi = rt->getActual()) {
                    if (tpsi->getUhdmType() ==
                        uhdm::UhdmType::IntegerTypespec) {
                      uhdm::IntegerTypespec* itps =
                          (uhdm::IntegerTypespec*)tpsi;
                      std::string_view v = itps->getValue();
                      v.remove_prefix(std::string_view("INT:").length());
                      int64_t index;
                      if (NumUtils::parseInt64(v, &index)) {
                        uhdm::Any* pattern = tp->getPattern();
                        if (pattern->getUhdmType() ==
                            uhdm::UhdmType::Constant) {
                          uhdm::Constant* c = (uhdm::Constant*)pattern;
                          uhdm::ExprEval eval;
                          int32_t val = eval.get_value(invalidValue, c);
                          if (index >= 0 && index < ((int64_t)size))
                            values[size - index - 1] = val;
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        } else {
          int32_t valIndex = 0;
          int32_t opIndex = 0;
          for (uhdm::Any* op : *operands) {
            uhdm::Expr* cop = (uhdm::Expr*)op;
            uhdm::ExprEval eval;
            uhdm::Expr* vexp = reduceExpr(
                cop, invalidValue, component, compileDesign, instance,
                fileSystem->toPathId(cop->getFile(), symbolTable),
                cop->getStartLine(), nullptr);
            uint64_t v = eval.get_uvalue(invalidValue, vexp);
            int32_t csize = adjustOpSize(tps, cop, opIndex, rhs, component,
                                         compileDesign, instance);
            if (invalidValue) {
              return result;
            }
            patternSize += csize;
            for (int32_t i = 0; i < csize; i++) {
              if (valIndex > (int32_t)(size - 1)) {
                break;
              }
              {
                int shift = (csize - 1 - i);
                if (shift < 0 || shift >= 64) {
                  return result;
                }
              }
              values[valIndex] = (v & (1ULL << (csize - 1 - i))) ? 1 : 0;
              valIndex++;
            }
            opIndex++;
          }
        }
      }
    }
  }
  for (uint32_t i = 0; i < size; i++) {
    if (vars && ((int32_t)i < (int32_t)(vars->size()))) {
      ((uhdm::Variables*)(*vars)[i])
          ->setValue("UINT:" + std::to_string(values[i]));
    }
  }

  if (tps->getUhdmType() == uhdm::UhdmType::PackedArrayTypespec) {
    const uhdm::PackedArrayTypespec* atps =
        (const uhdm::PackedArrayTypespec*)tps;
    const uhdm::Typespec* etps = nullptr;
    if (const uhdm::RefTypespec* rt = atps->getElemTypespec()) {
      etps = rt->getActual();
    }
    if (etps != nullptr) {
      uhdm::UhdmType etps_type = etps->getUhdmType();
      if (size > 1) {
        if (etps_type == uhdm::UhdmType::EnumTypespec) {
          uhdm::PackedArrayVar* array = s.make<uhdm::PackedArrayVar>();
          array->setSize(size);
          array->setRanges(atps->getRanges());
          array->setElements(vars);
          for (uint32_t i = 0; i < size; i++) {
            vars->emplace_back(s.make<uhdm::EnumVar>());
          }
          result = array;
        }
      }
    }
  } else if (tps->getUhdmType() == uhdm::UhdmType::LogicTypespec) {
    if (patternSize) {
      uhdm::Constant* c = s.make<uhdm::Constant>();
      c->setFile(rhs->getFile());
      c->setStartLine(rhs->getStartLine());
      c->setStartColumn(rhs->getStartColumn());
      c->setEndLine(rhs->getEndLine());
      c->setEndColumn(rhs->getEndColumn());
      result = c;
      uint64_t value = 0;
      for (uint64_t i = 0; i < patternSize; i++) {
        value |= (values[i]) ? ((uint64_t)1 << (patternSize - 1 - i)) : 0;
      }
      result->setSize(size);
      result->setValue("UINT:" + std::to_string(value));
      result->setDecompile(std::to_string(size) + "\'d" +
                           std::to_string(value));
    }
  }
  return result;
}

bool CompileHelper::valueRange(Value* val, const uhdm::Typespec* lhstps,
                               const uhdm::Typespec* rhstps,
                               DesignComponent* component,
                               CompileDesign* compileDesign,
                               ValuedComponentI* instance) {
  if (!lhstps || !rhstps) return false;
  uhdm::Range* r = nullptr;
  uhdm::UhdmType type = lhstps->getUhdmType();
  switch (type) {
    case uhdm::UhdmType::LogicTypespec: {
      uhdm::LogicTypespec* lts = (uhdm::LogicTypespec*)lhstps;
      if (lts->getRanges() && !lts->getRanges()->empty()) {
        r = (*lts->getRanges())[0];
      }
      break;
    }
    case uhdm::UhdmType::ArrayTypespec: {
      uhdm::ArrayTypespec* lts = (uhdm::ArrayTypespec*)lhstps;
      if (lts->getRanges() && !lts->getRanges()->empty()) {
        r = (*lts->getRanges())[0];
      }
      break;
    }
    case uhdm::UhdmType::PackedArrayTypespec: {
      uhdm::PackedArrayTypespec* lts = (uhdm::PackedArrayTypespec*)lhstps;
      if (lts->getRanges() && !lts->getRanges()->empty()) {
        r = (*lts->getRanges())[0];
      }
      break;
    }
    case uhdm::UhdmType::BitTypespec: {
      uhdm::BitTypespec* lts = (uhdm::BitTypespec*)lhstps;
      if (lts->getRanges() && !lts->getRanges()->empty()) {
        r = (*lts->getRanges())[0];
      }
      break;
    }
    case uhdm::UhdmType::IntTypespec: {
      uhdm::IntTypespec* lts = (uhdm::IntTypespec*)lhstps;
      if (lts->getRanges() && !lts->getRanges()->empty()) {
        r = (*lts->getRanges())[0];
      }
      break;
    }
    default:
      break;
  }
  bool isSigned = false;
  type = rhstps->getUhdmType();
  switch (type) {
    case uhdm::UhdmType::LogicTypespec: {
      uhdm::LogicTypespec* tps = (uhdm::LogicTypespec*)rhstps;
      isSigned = tps->getSigned();
      break;
    }
    case uhdm::UhdmType::BitTypespec: {
      uhdm::BitTypespec* tps = (uhdm::BitTypespec*)rhstps;
      isSigned = tps->getSigned();
      break;
    }
    case uhdm::UhdmType::IntTypespec: {
      uhdm::IntTypespec* tps = (uhdm::IntTypespec*)rhstps;
      isSigned = tps->getSigned();
      break;
    }
    default:
      break;
  }
  if (r) {
    bool invalidValue = false;
    uhdm::Expr* lv =
        reduceExpr((uhdm::Any*)r->getLeftExpr(), invalidValue, component,
                   compileDesign, instance, BadPathId, 0, nullptr, true);
    uhdm::Expr* rv =
        reduceExpr((uhdm::Any*)r->getRightExpr(), invalidValue, component,
                   compileDesign, instance, BadPathId, 0, nullptr, true);
    uhdm::ExprEval eval;
    int64_t lvv = eval.get_value(invalidValue, lv);
    int64_t rvv = eval.get_value(invalidValue, rv);
    if (invalidValue == false) {
      val->setRange(lvv, rvv);
    }
  }
  val->setSigned(isSigned);
  return false;
}

void CompileHelper::setRange(uhdm::Constant* c, Value* val,
                             CompileDesign* compileDesign) {
  if (!val || !c) return;
  uhdm::Serializer& s = compileDesign->getSerializer();
  uint16_t lr = val->getLRange();
  uint16_t rr = val->getRRange();
  if (lr || rr) {
    uhdm::LogicTypespec* tps = s.make<uhdm::LogicTypespec>();
    uhdm::RefTypespec* tpsRef = s.make<uhdm::RefTypespec>();
    tpsRef->setParent(c);
    tpsRef->setActual(tps);
    c->setTypespec(tpsRef);
    uhdm::Range* r = s.make<uhdm::Range>();
    r->setParent(tps);
    tps->getRanges(true)->emplace_back(r);
    uhdm::Constant* lc = s.make<uhdm::Constant>();
    lc->setValue("UINT:" + std::to_string(lr));
    r->setLeftExpr(lc);
    uhdm::Constant* rc = s.make<uhdm::Constant>();
    rc->setValue("UINT:" + std::to_string(rr));
    r->setRightExpr(rc);
  }
}

void CompileHelper::compileLetDeclaration(DesignComponent* component,
                                          const FileContent* fC,
                                          NodeId Let_declaration,
                                          CompileDesign* compileDesign) {
  uhdm::Serializer& s = compileDesign->getSerializer();
  NodeId nameId = fC->Child(Let_declaration);
  const std::string_view name = fC->SymName(nameId);
  NodeId Let_port_list = fC->Sibling(nameId);
  NodeId Expression;
  if (fC->Type(Let_port_list) == VObjectType::paLet_port_list) {
    Expression = fC->Sibling(Let_port_list);
  } else {
    Expression = Let_port_list;
  }
  uhdm::LetDecl* decl = s.make<uhdm::LetDecl>();
  decl->setName(name);
  decl->setParent(component->getUhdmModel());
  fC->populateCoreMembers(nameId, nameId, decl);
  if (auto ios = compileTfPortList(component, decl, fC, Let_port_list,
                                   compileDesign)) {
    uhdm::SeqFormalDeclCollection* args = decl->getSeqFormalDecls(true);
    for (auto io : *ios) {
      uhdm::SeqFormalDecl* formal = s.make<uhdm::SeqFormalDecl>();
      formal->setName(io->getName());
      formal->setParent(decl);
      formal->setFile(io->getFile());
      formal->setStartLine(io->getStartLine());
      formal->setStartColumn(io->getStartColumn());
      formal->setEndLine(io->getEndLine());
      formal->setEndColumn(io->getEndColumn());
      args->emplace_back(formal);
    }
  }

  LetStmt* stmt = nullptr;
  if (uhdm::Expr* exp = (uhdm::Expr*)compileExpression(
          component, fC, Expression, compileDesign, Reduce::No, decl, nullptr,
          false)) {
    decl->getExprs(true)->emplace_back(exp);

    stmt = new LetStmt(decl, decl->getSeqFormalDecls(), exp);
  } else {
    stmt = new LetStmt(decl, decl->getSeqFormalDecls(), nullptr);
  }
  component->insertLetStmt(name, stmt);
}

bool CompileHelper::elaborationSystemTask(DesignComponent* component,
                                          const FileContent* fC, NodeId id,
                                          CompileDesign* compileDesign) {
  SymbolTable* const symbols = m_session->getSymbolTable();
  ErrorContainer* const errors = m_session->getErrorContainer();
  NodeId taskNameId = fC->Child(id);
  NodeId NumberOrArgList = fC->Sibling(taskNameId);
  NodeId ArgList = NumberOrArgList;
  if (fC->Type(ArgList) != VObjectType::paList_of_arguments) {
    ArgList = fC->Sibling(ArgList);
  }
  NodeId Expression = fC->Child(ArgList);
  NodeId Primary = fC->Child(Expression);
  NodeId Primary_literal = fC->Child(Primary);
  NodeId StringId = fC->Child(Primary_literal);
  std::string_view text = fC->SymName(StringId);
  std::string_view name = fC->SymName(taskNameId);
  uhdm::Serializer& s = compileDesign->getSerializer();
  uhdm::SysTaskCall* scall = s.make<uhdm::SysTaskCall>();
  fC->populateCoreMembers(id, id, scall);
  scall->setName(name);
  uhdm::AnyCollection* args = scall->getArguments(true);
  uhdm::Constant* c = s.make<uhdm::Constant>();
  args->emplace_back(c);
  c->setValue(std::string("STRING:") + std::string(text));
  c->setDecompile(text);
  c->setConstType(vpiStringConst);
  component->addElabSysCall(scall);
  Location loc(fC->getFileId(id), fC->Line(id), fC->Column(id),
               symbols->registerSymbol(text));
  if (name == "fatal") {
    errors->addError(ErrorDefinition::ELAB_SYSTEM_FATAL, loc);
  } else if (name == "error") {
    errors->addError(ErrorDefinition::ELAB_SYSTEM_ERROR, loc);
  }
  if (name == "warning") {
    errors->addError(ErrorDefinition::ELAB_SYSTEM_WARNING, loc);
  }
  if (name == "info") {
    errors->addError(ErrorDefinition::ELAB_SYSTEM_INFO, loc);
  }
  return true;
}

}  // namespace SURELOG
