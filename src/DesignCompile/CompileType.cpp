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
 * File:   CompileExpression.cpp
 * Author: alain
 *
 * Created on May 14, 2019, 8:03 PM
 */

#include <Surelog/CommandLine/CommandLineParser.h>
#include <Surelog/Design/DataType.h>
#include <Surelog/Design/DummyType.h>
#include <Surelog/Design/Enum.h>
#include <Surelog/Design/FileContent.h>
#include <Surelog/Design/Function.h>
#include <Surelog/Design/ModuleDefinition.h>
#include <Surelog/Design/ModuleInstance.h>
#include <Surelog/Design/Netlist.h>
#include <Surelog/Design/ParamAssign.h>
#include <Surelog/Design/Parameter.h>
#include <Surelog/Design/SimpleType.h>
#include <Surelog/Design/Struct.h>
#include <Surelog/Design/Task.h>
#include <Surelog/Design/Union.h>
#include <Surelog/DesignCompile/CompileDesign.h>
#include <Surelog/DesignCompile/CompileHelper.h>
#include <Surelog/Library/Library.h>
#include <Surelog/Package/Package.h>
#include <Surelog/SourceCompile/Compiler.h>
#include <Surelog/SourceCompile/SymbolTable.h>
#include <Surelog/Testbench/ClassDefinition.h>
#include <Surelog/Testbench/TypeDef.h>
#include <Surelog/Testbench/Variable.h>
#include <Surelog/Utils/FileUtils.h>
#include <Surelog/Utils/StringUtils.h>

// UHDM
#include <uhdm/ElaboratorListener.h>
#include <uhdm/ExprEval.h>
#include <uhdm/clone_tree.h>
#include <uhdm/uhdm.h>

#include <stack>

namespace SURELOG {

using namespace UHDM;  // NOLINT (using a bunch of them)
namespace fs = std::filesystem;

variables* CompileHelper::getSimpleVarFromTypespec(
    UHDM::typespec* spec, std::vector<UHDM::range*>* packedDimensions,
    CompileDesign* compileDesign) {
  Serializer& s = compileDesign->getSerializer();
  variables* var = nullptr;
  UHDM_OBJECT_TYPE ttps = spec->UhdmType();
  switch (ttps) {
    case uhdmint_typespec: {
      UHDM::int_var* int_var = s.MakeInt_var();
      var = int_var;
      break;
    }
    case uhdminteger_typespec: {
      UHDM::integer_var* integer_var = s.MakeInteger_var();
      var = integer_var;
      break;
    }
    case uhdmlong_int_typespec: {
      UHDM::long_int_var* int_var = s.MakeLong_int_var();
      var = int_var;
      break;
    }
    case uhdmstring_typespec: {
      UHDM::string_var* int_var = s.MakeString_var();
      var = int_var;
      break;
    }
    case uhdmshort_int_typespec: {
      UHDM::short_int_var* int_var = s.MakeShort_int_var();
      var = int_var;
      break;
    }
    case uhdmbyte_typespec: {
      UHDM::byte_var* int_var = s.MakeByte_var();
      var = int_var;
      break;
    }
    case uhdmreal_typespec: {
      UHDM::real_var* int_var = s.MakeReal_var();
      var = int_var;
      break;
    }
    case uhdmshort_real_typespec: {
      UHDM::short_real_var* int_var = s.MakeShort_real_var();
      var = int_var;
      break;
    }
    case uhdmtime_typespec: {
      UHDM::time_var* int_var = s.MakeTime_var();
      var = int_var;
      break;
    }
    case uhdmbit_typespec: {
      UHDM::bit_var* int_var = s.MakeBit_var();
      int_var->Ranges(packedDimensions);
      var = int_var;
      break;
    }
    case uhdmenum_typespec: {
      UHDM::enum_var* enum_var = s.MakeEnum_var();
      var = enum_var;
      enum_var->Typespec(spec);
      if (packedDimensions) {
        packed_array_var* array = s.MakePacked_array_var();
        VectorOfany* vars = s.MakeAnyVec();
        array->Ranges(packedDimensions);
        array->Elements(vars);
        vars->push_back(var);
        var = array;
      }
      break;
    }
    case uhdmlogic_typespec:
    case uhdmvoid_typespec: {
      logic_var* logicv = s.MakeLogic_var();
      logicv->Ranges(packedDimensions);
      var = logicv;
      break;
    }
    case uhdmunion_typespec: {
      UHDM::union_var* unionv = s.MakeUnion_var();
      var = unionv;
      var->Typespec(spec);
      if (packedDimensions) {
        packed_array_var* array = s.MakePacked_array_var();
        VectorOfany* vars = s.MakeAnyVec();
        array->Ranges(packedDimensions);
        array->Elements(vars);
        vars->push_back(var);
        var = array;
      }
      break;
    }
    case uhdmstruct_typespec: {
      UHDM::struct_var* structv = s.MakeStruct_var();
      var = structv;
      var->Typespec(spec);
      if (packedDimensions) {
        packed_array_var* array = s.MakePacked_array_var();
        VectorOfany* vars = s.MakeAnyVec();
        array->Ranges(packedDimensions);
        array->Elements(vars);
        vars->push_back(var);
        var = array;
      }
      break;
    }
    case uhdmarray_typespec: {
      UHDM::array_var* array = s.MakeArray_var();
      var = array;
      break;
    }
    default:
      break;
  }
  if (var) {
    var->Typespec(spec);
  }
  return var;
}

UHDM::any* CompileHelper::compileVariable(
    DesignComponent* component, const FileContent* fC, NodeId declarationId,
    CompileDesign* compileDesign, UHDM::any* pstmt,
    SURELOG::ValuedComponentI* instance, bool reduce, bool muteErrors) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::any* result = nullptr;
  NodeId variable = declarationId;
  if (fC->Type(variable) == VObjectType::slData_type) {
    variable = fC->Child(variable);
  }
  NodeId nameId = fC->Sibling(variable);
  VObjectType the_type = fC->Type(variable);
  if (the_type == VObjectType::slData_type ||
      the_type == VObjectType::slPs_or_hierarchical_identifier) {
    variable = fC->Child(variable);
    the_type = fC->Type(variable);
  } else if (the_type == VObjectType::slNull_rule) {
    return nullptr;
  }
  if (the_type == VObjectType::slComplex_func_call) {
    variable = fC->Child(variable);
    the_type = fC->Type(variable);
  }
  NodeId Packed_dimension = fC->Sibling(variable);
  if (Packed_dimension == 0) {
    // Implicit return value:
    // function [1:0] fct();
    if (fC->Type(variable) == slConstant_range) {
      Packed_dimension = variable;
    }
  }
  int size;
  VectorOfrange* ranges =
      compileRanges(component, fC, Packed_dimension, compileDesign, pstmt,
                    instance, reduce, size, muteErrors);
  switch (the_type) {
    case VObjectType::slStringConst:
    case VObjectType::slChandle_type: {
      const std::string& typeName = fC->SymName(variable);

      if (const DataType* dt = component->getDataType(typeName)) {
        dt = dt->getActual();
        typespec* tps = dt->getTypespec();
        if (tps) {
          variables* var = getSimpleVarFromTypespec(tps, ranges, compileDesign);
          if (var) var->VpiName(fC->SymName(variable));
          result = var;
        }
      }
      if (result == nullptr) {
        if (the_type == slChandle_type) {
          result = s.MakeChandle_var();
        } else {
          ref_var* ref = s.MakeRef_var();
          ref->VpiName(typeName);
          result = ref;
        }
      }
      break;
    }
    case VObjectType::slIntVec_TypeLogic:
    case VObjectType::slIntVec_TypeReg: {
      logic_var* var = s.MakeLogic_var();
      var->Ranges(ranges);
      var->VpiFile(fC->getFileName());
      var->VpiLineNo(fC->Line(declarationId));
      var->VpiColumnNo(fC->Column(declarationId));
      var->VpiEndLineNo(fC->EndLine(declarationId));
      var->VpiEndColumnNo(fC->EndColumn(declarationId));
      result = var;
      break;
    }
    case VObjectType::slIntegerAtomType_Int: {
      int_var* var = s.MakeInt_var();
      result = var;
      break;
    }
    case VObjectType::slIntegerAtomType_Integer: {
      integer_var* var = s.MakeInteger_var();
      result = var;
      break;
    }
    case VObjectType::slSigning_Unsigned: {
      int_var* var = s.MakeInt_var();
      result = var;
      break;
    }
    case VObjectType::slIntegerAtomType_Byte: {
      byte_var* var = s.MakeByte_var();
      result = var;
      break;
    }
    case VObjectType::slIntegerAtomType_LongInt: {
      long_int_var* var = s.MakeLong_int_var();
      result = var;
      break;
    }
    case VObjectType::slIntegerAtomType_Shortint: {
      short_int_var* var = s.MakeShort_int_var();
      result = var;
      break;
    }
    case VObjectType::slIntegerAtomType_Time: {
      time_var* var = s.MakeTime_var();
      result = var;
      break;
    }
    case VObjectType::slIntVec_TypeBit: {
      bit_var* var = s.MakeBit_var();
      var->Ranges(ranges);
      result = var;
      break;
    }
    case VObjectType::slNonIntType_ShortReal: {
      short_real_var* var = s.MakeShort_real_var();
      result = var;
      break;
    }
    case VObjectType::slNonIntType_Real: {
      real_var* var = s.MakeReal_var();
      result = var;
      break;
    }
    case VObjectType::slClass_scope: {
      NodeId class_type = fC->Child(variable);
      NodeId class_name = fC->Child(class_type);
      const std::string& packageName = fC->SymName(class_name);
      Design* design = compileDesign->getCompiler()->getDesign();
      NodeId symb_id = fC->Sibling(variable);
      const std::string& typeName = fC->SymName(symb_id);
      Package* pack = design->getPackage(packageName);
      variables* var = nullptr;
      if (pack) {
        const DataType* dtype = pack->getDataType(typeName);
        while (dtype) {
          typespec* tps = dtype->getTypespec();
          if (tps) {
            var = getSimpleVarFromTypespec(tps, ranges, compileDesign);
            break;
          }
          dtype = dtype->getDefinition();
        }
      }
      const std::string completeName = packageName + "::" + typeName;
      if (var == nullptr) var = s.MakeClass_var();
      var->VpiName(completeName);
      result = var;
      break;
    }
    case VObjectType::slString_type: {
      string_var* var = s.MakeString_var();
      result = var;
      break;
    }
    case VObjectType::slVariable_lvalue: {
      NodeId hier_ident = fC->Child(variable);
      NodeId nameid = fC->Child(hier_ident);
      int_var* var = s.MakeInt_var();
      var->VpiName(fC->SymName(nameid));
      result = var;
      break;
    }
    default: {
      // Implicit type
      logic_var* var = s.MakeLogic_var();
      var->Ranges(ranges);
      result = var;
      break;
    }
  }
  if (result && (result->VpiLineNo() == 0)) {
    NodeId id = nameId ? nameId : variable;
    result->VpiFile(fC->getFileName());
    result->VpiLineNo(fC->Line(id));
    result->VpiColumnNo(fC->Column(id));
    result->VpiEndLineNo(fC->EndLine(id));
    result->VpiEndColumnNo(fC->EndColumn(id));
  }
  return result;
}

const UHDM::typespec* bindTypespec(const std::string& name,
                                   SURELOG::ValuedComponentI* instance,
                                   Serializer& s) {
  const typespec* result = nullptr;
  ModuleInstance* modInst = valuedcomponenti_cast<ModuleInstance*>(instance);
  while (modInst) {
    for (Parameter* param : modInst->getTypeParams()) {
      const std::string& pname = param->getName();
      if (pname == name) {
        any* uparam = param->getUhdmParam();
        if (uparam) {
          type_parameter* tparam = any_cast<type_parameter*>(uparam);
          if (tparam) {
            result = tparam->Typespec();
            ElaboratorListener listener(&s);
            result = any_cast<typespec*>(
                UHDM::clone_tree((any*)result, s, &listener));
          }
        }
        break;
      }
    }
    if (result == nullptr) {
      ModuleDefinition* mod = (ModuleDefinition*)modInst->getDefinition();
      if (mod) {
        Parameter* param = mod->getParameter(name);
        if (param) {
          any* uparam = param->getUhdmParam();
          if (uparam) {
            type_parameter* tparam = any_cast<type_parameter*>(uparam);
            if (tparam) {
              result = tparam->Typespec();
              ElaboratorListener listener(&s);
              result = any_cast<typespec*>(
                  UHDM::clone_tree((any*)result, s, &listener));
            }
          }
        }
        const DataType* dt = mod->getDataType(name);
        if (dt) {
          dt = dt->getActual();
          result = dt->getTypespec();
          ElaboratorListener listener(&s);
          result =
              any_cast<typespec*>(UHDM::clone_tree((any*)result, s, &listener));
        }
      }
    }
    modInst = modInst->getParent();
  }
  return result;
}

typespec* CompileHelper::compileDatastructureTypespec(
    DesignComponent* component, const FileContent* fC, NodeId type,
    CompileDesign* compileDesign, SURELOG::ValuedComponentI* instance,
    bool reduce, const std::string& suffixname, const std::string& typeName) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  typespec* result = nullptr;
  if (component) {
    const DataType* dt = component->getDataType(typeName);
    if (dt == nullptr) {
      std::string libName = fC->getLibrary()->getName();
      dt = compileDesign->getCompiler()->getDesign()->getClassDefinition(
          libName + "@" + typeName);
      if (dt == nullptr) {
        dt = compileDesign->getCompiler()->getDesign()->getClassDefinition(
            component->getName() + "::" + typeName);
      }
      if (dt == nullptr) {
        if (component->getParentScope())
          dt = compileDesign->getCompiler()->getDesign()->getClassDefinition(
              ((DesignComponent*)component->getParentScope())->getName() +
              "::" + typeName);
      }
      if (dt == nullptr) {
        dt = compileDesign->getCompiler()->getDesign()->getClassDefinition(
            typeName);
      }
      if (dt == nullptr) {
        Parameter* p = component->getParameter(typeName);
        if (p && p->getUhdmParam() &&
            (p->getUhdmParam()->UhdmType() == uhdmtype_parameter))
          dt = p;
      }
      if (dt == nullptr) {
        for (ParamAssign* passign : component->getParamAssignVec()) {
          const FileContent* fCP = passign->getFileContent();
          if (fCP->SymName(passign->getParamId()) == typeName) {
            UHDM::param_assign* param_assign = passign->getUhdmParamAssign();
            UHDM::parameter* lhs = (UHDM::parameter*)param_assign->Lhs();
            result = (typespec*)lhs->Typespec();
            if (result == nullptr) {
              int_typespec* tps =
                  buildIntTypespec(compileDesign, fC->getFileName(), typeName,
                                   "", fC->Line(type), fC->Column(type),
                                   fC->EndLine(type), fC->EndColumn(type));
              lhs->Typespec(tps);
              result = tps;
            }
            if (result->UhdmType() == uhdmint_typespec) {
              int_typespec* ts = (int_typespec*)result;
              ref_obj* ref = s.MakeRef_obj();
              ref->Actual_group(lhs);
              ts->Cast_to_expr(ref);
            }
            return result;
          }
        }
      }
      if (dt == nullptr) {
        for (Signal* sig : component->getPorts()) {
          // Interface port type
          if (sig->getName() == typeName) {
            if (sig->getInterfaceTypeNameId()) {
              std::string suffixname;
              std::string typeName;
              if (fC->Type(sig->getInterfaceTypeNameId()) == slStringConst) {
                typeName = fC->SymName(sig->getInterfaceTypeNameId());
              }
              NodeId suffixNode = 0;
              if ((suffixNode = fC->Sibling(type))) {
                if (fC->Type(suffixNode) == slStringConst) {
                  suffixname = fC->SymName(suffixNode);
                } else if (fC->Type(suffixNode) == slConstant_bit_select) {
                  suffixNode = fC->Sibling(suffixNode);
                  if (fC->Type(suffixNode) == slStringConst) {
                    suffixname = fC->SymName(suffixNode);
                  }
                }
              }
              typespec* tmp = compileDatastructureTypespec(
                  component, fC, sig->getInterfaceTypeNameId(), compileDesign,
                  instance, reduce, suffixname, typeName);
              if (tmp) {
                if (tmp->UhdmType() == uhdminterface_typespec) {
                  if (!suffixname.empty()) {
                    ErrorContainer* errors =
                        compileDesign->getCompiler()->getErrorContainer();
                    SymbolTable* symbols =
                        compileDesign->getCompiler()->getSymbolTable();
                    Location loc1(
                        symbols->registerSymbol(fC->getFileName().string()),
                        fC->Line(suffixNode), fC->Column(suffixNode),
                        symbols->registerSymbol(suffixname));
                    std::string libName = fC->getLibrary()->getName();
                    Design* design = compileDesign->getCompiler()->getDesign();
                    ModuleDefinition* def =
                        design->getModuleDefinition(libName + "@" + typeName);
                    const FileContent* interF = def->getFileContents()[0];
                    Location loc2(
                        symbols->registerSymbol(interF->getFileName().string()),
                        interF->Line(def->getNodeIds()[0]),
                        interF->Column(def->getNodeIds()[0]),
                        symbols->registerSymbol(typeName));
                    Error err(ErrorDefinition::ELAB_UNKNOWN_INTERFACE_MEMBER,
                              loc1, loc2);
                    errors->addError(err);
                  }
                }
                return tmp;
              }
            }
          }
        }
      }
    }
    if (dt == nullptr) {
      if (!compileDesign->getCompiler()->getCommandLineParser()->fileunit()) {
        for (auto fC :
             compileDesign->getCompiler()->getDesign()->getAllFileContents()) {
          if (const DataType* dt1 = fC.second->getDataType(typeName)) {
            dt = dt1;
            break;
          }
        }
      }
    }

    TypeDef* parent_tpd = nullptr;
    while (dt) {
      if (const TypeDef* tpd = datatype_cast<const TypeDef*>(dt)) {
        parent_tpd = (TypeDef*)tpd;
        if (parent_tpd->getTypespec()) {
          result = parent_tpd->getTypespec();
          break;
        }
      } else if (const Struct* st = datatype_cast<const Struct*>(dt)) {
        result = st->getTypespec();
        if (!suffixname.empty()) {
          struct_typespec* tpss = (struct_typespec*)result;
          for (typespec_member* memb : *tpss->Members()) {
            if (memb->VpiName() == suffixname) {
              result = (UHDM::typespec*)memb->Typespec();
              break;
            }
          }
        }
        break;
      } else if (const Enum* en = datatype_cast<const Enum*>(dt)) {
        result = en->getTypespec();
        break;
      } else if (const Union* un = datatype_cast<const Union*>(dt)) {
        result = un->getTypespec();
        break;
      } else if (const DummyType* un = datatype_cast<const DummyType*>(dt)) {
        result = un->getTypespec();
      } else if (const SimpleType* sit = datatype_cast<const SimpleType*>(dt)) {
        result = sit->getTypespec();
        if (parent_tpd && result) {
          ElaboratorListener listener(&s);
          typespec* new_result =
              any_cast<typespec*>(UHDM::clone_tree((any*)result, s, &listener));
          if (new_result) {
            new_result->Typedef_alias(result);
            result = new_result;
          }
        }
        break;
      } else if (/*const Parameter* par = */ datatype_cast<const Parameter*>(
          dt)) {
        // Prevent circular definition
        return nullptr;
      } else if (const ClassDefinition* classDefn =
                     datatype_cast<const ClassDefinition*>(dt)) {
        class_typespec* ref = s.MakeClass_typespec();
        ref->Class_defn(classDefn->getUhdmDefinition());
        ref->VpiName(typeName);
        ref->VpiFile(fC->getFileName());
        ref->VpiLineNo(fC->Line(type));
        ref->VpiColumnNo(fC->Column(type));
        ref->VpiEndLineNo(fC->EndLine(type));
        ref->VpiEndColumnNo(fC->EndColumn(type));
        result = ref;

        const FileContent* actualFC = fC;
        NodeId param = fC->Sibling(type);
        if (parent_tpd) {
          actualFC = parent_tpd->getFileContent();
          NodeId n = parent_tpd->getDefinitionNode();
          param = actualFC->Sibling(n);
        }
        if (param &&
            (actualFC->Type(param) != slList_of_net_decl_assignments)) {
          VectorOfany* params = s.MakeAnyVec();
          ref->Parameters(params);
          VectorOfparam_assign* assigns = s.MakeParam_assignVec();
          ref->Param_assigns(assigns);
          unsigned int index = 0;
          NodeId Parameter_value_assignment = param;
          NodeId List_of_parameter_assignments =
              actualFC->Child(Parameter_value_assignment);
          NodeId Ordered_parameter_assignment =
              actualFC->Child(List_of_parameter_assignments);
          if (Ordered_parameter_assignment &&
              (actualFC->Type(Ordered_parameter_assignment) ==
               slOrdered_parameter_assignment)) {
            while (Ordered_parameter_assignment) {
              NodeId Param_expression =
                  actualFC->Child(Ordered_parameter_assignment);
              NodeId Data_type = actualFC->Child(Param_expression);
              std::string fName;
              const DesignComponent::ParameterVec& formal =
                  classDefn->getOrderedParameters();
              any* fparam = nullptr;
              if (index < formal.size()) {
                Parameter* p = formal.at(index);
                fName = p->getName();
                fparam = p->getUhdmParam();

                if (actualFC->Type(Data_type) == slData_type) {
                  typespec* tps =
                      compileTypespec(component, actualFC, Data_type,
                                      compileDesign, result, instance, reduce);

                  type_parameter* tp = s.MakeType_parameter();
                  tp->VpiName(fName);
                  tp->VpiParent(ref);
                  tps->VpiParent(tp);
                  tp->Typespec(tps);
                  params->push_back(tp);
                  param_assign* pass = s.MakeParam_assign();
                  pass->Rhs(tp);
                  pass->Lhs(fparam);
                  assigns->push_back(pass);
                } else {
                  any* exp = compileExpression(component, actualFC,
                                               Param_expression, compileDesign,
                                               nullptr, instance, reduce);
                  if (exp) {
                    if (exp->UhdmType() == uhdmref_obj) {
                      const std::string& name = ((ref_obj*)exp)->VpiName();
                      typespec* tps = compileDatastructureTypespec(
                          component, actualFC, param, compileDesign, instance,
                          reduce, "", name);
                      if (tps) {
                        type_parameter* tp = s.MakeType_parameter();
                        tp->VpiName(fName);
                        tp->Typespec(tps);
                        tps->VpiParent(tp);
                        tp->VpiParent(ref);
                        params->push_back(tp);
                        param_assign* pass = s.MakeParam_assign();
                        pass->Rhs(tp);
                        pass->Lhs(fparam);
                        assigns->push_back(pass);
                      }
                    }
                  }
                }
              }
              Ordered_parameter_assignment =
                  actualFC->Sibling(Ordered_parameter_assignment);
              index++;
            }
          }
        }
        break;
      }
      // if (result)
      //  break;
      dt = dt->getDefinition();
    }

    if (result == nullptr) {
      std::string libName = fC->getLibrary()->getName();
      Design* design = compileDesign->getCompiler()->getDesign();
      ModuleDefinition* def =
          design->getModuleDefinition(libName + "@" + typeName);
      if (def) {
        if (def->getType() == slInterface_declaration) {
          interface_typespec* tps = s.MakeInterface_typespec();
          tps->VpiName(typeName);
          tps->VpiFile(fC->getFileName());
          tps->VpiLineNo(fC->Line(type));
          tps->VpiColumnNo(fC->Column(type));
          tps->VpiEndLineNo(fC->EndLine(type));
          tps->VpiEndColumnNo(fC->EndColumn(type));
          result = tps;
          if (!suffixname.empty()) {
            const DataType* defType = def->getDataType(suffixname);
            bool foundDataType = false;
            while (defType) {
              foundDataType = true;
              if (typespec* t = defType->getTypespec()) {
                result = t;
                return result;
              }
              defType = defType->getDefinition();
            }
            if (foundDataType) {
              // The binding to the actual typespec is still incomplete
              result = s.MakeLogic_typespec();
              return result;
            }
          }
          if (NodeId sub = fC->Sibling(type)) {
            const std::string& name = fC->SymName(sub);
            if (def->getModPort(name)) {
              interface_typespec* mptps = s.MakeInterface_typespec();
              mptps->VpiName(name);
              mptps->VpiFile(fC->getFileName());
              mptps->VpiLineNo(fC->Line(type));
              mptps->VpiColumnNo(fC->Column(type));
              mptps->VpiEndLineNo(fC->EndLine(type));
              mptps->VpiEndColumnNo(fC->EndColumn(type));
              mptps->VpiParent(tps);
              mptps->VpiIsModPort(true);
              result = mptps;
            }
          }
        }
      }
    }

    if (result == nullptr) {
      unsupported_typespec* tps = s.MakeUnsupported_typespec();
      tps->VpiName(typeName);
      tps->VpiFile(fC->getFileName());
      tps->VpiLineNo(fC->Line(type));
      tps->VpiColumnNo(fC->Column(type));
      tps->VpiEndLineNo(fC->EndLine(type));
      tps->VpiEndColumnNo(fC->EndColumn(type));
      result = tps;
    }
  } else {
    unsupported_typespec* tps = s.MakeUnsupported_typespec();
    tps->VpiName(typeName);
    tps->VpiFile(fC->getFileName());
    tps->VpiLineNo(fC->Line(type));
    tps->VpiColumnNo(fC->Column(type));
    tps->VpiEndLineNo(fC->EndLine(type));
    tps->VpiEndColumnNo(fC->EndColumn(type));
    result = tps;
  }
  return result;
}

UHDM::typespec_member* CompileHelper::buildTypespecMember(
    CompileDesign* compileDesign, const fs::path& fileName,
    const std::string& name, const std::string& value, unsigned int line,
    unsigned short column, unsigned int eline, unsigned short ecolumn) {
  /*
  std::string hash = fileName + ":" + name + ":" + value + ":" +
  std::to_string(line) + ":" + std::to_string(column) + ":" +
  std::to_string(eline) + ":" + std::to_string(ecolumn);
  std::unordered_map<std::string, UHDM::typespec_member*>::iterator itr =
      m_cache_typespec_member.find(hash);
  */
  typespec_member* var = nullptr;
  // if (itr == m_cache_typespec_member.end()) {
  Serializer& s = compileDesign->getSerializer();
  var = s.MakeTypespec_member();
  var->VpiName(name);
  var->VpiFile(fileName);
  var->VpiLineNo(line);
  var->VpiColumnNo(column);
  var->VpiEndLineNo(eline);
  var->VpiEndColumnNo(ecolumn);
  //  m_cache_typespec_member.insert(std::make_pair(hash, var));
  //} else {
  //  var = (*itr).second;
  //}
  return var;
}

int_typespec* CompileHelper::buildIntTypespec(
    CompileDesign* compileDesign, const fs::path& fileName,
    const std::string& name, const std::string& value, unsigned int line,
    unsigned short column, unsigned int eline, unsigned short ecolumn) {
  /*
  std::string hash = fileName + ":" + name + ":" + value + ":" +
  std::to_string(line)  + ":" + std::to_string(column) + ":" +
  std::to_string(eline) + ":" + std::to_string(ecolumn);
  std::unordered_map<std::string, UHDM::int_typespec*>::iterator itr =
      m_cache_int_typespec.find(hash);
  */
  int_typespec* var = nullptr;
  // if (itr == m_cache_int_typespec.end()) {
  Serializer& s = compileDesign->getSerializer();
  var = s.MakeInt_typespec();
  var->VpiValue(value);
  var->VpiName(name);
  var->VpiFile(fileName);
  var->VpiLineNo(line);
  var->VpiColumnNo(column);
  var->VpiEndLineNo(eline);
  var->VpiEndColumnNo(ecolumn);
  //  m_cache_int_typespec.insert(std::make_pair(hash, var));
  //} else {
  //  var = (*itr).second;
  //}
  return var;
}

UHDM::typespec* CompileHelper::compileBuiltinTypespec(
    DesignComponent* component, const FileContent* fC, NodeId type,
    VObjectType the_type, CompileDesign* compileDesign, VectorOfrange* ranges) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  typespec* result = nullptr;
  NodeId sign = fC->Sibling(type);
  bool isSigned = true;
  if (sign && (fC->Type(sign) == slSigning_Unsigned)) {
    isSigned = false;
  }
  switch (the_type) {
    case VObjectType::slIntVec_TypeLogic:
    case VObjectType::slIntVec_TypeReg: {
      logic_typespec* var = s.MakeLogic_typespec();
      var->Ranges(ranges);
      var->VpiFile(fC->getFileName());
      var->VpiLineNo(fC->Line(type));
      var->VpiColumnNo(fC->Column(type));
      var->VpiEndLineNo(fC->EndLine(type));
      var->VpiEndColumnNo(fC->EndColumn(type));
      result = var;
      break;
    }
    case VObjectType::slIntegerAtomType_Int: {
      int_typespec* var = s.MakeInt_typespec();
      var->VpiSigned(isSigned);
      var->VpiFile(fC->getFileName());
      var->VpiLineNo(fC->Line(type));
      var->VpiColumnNo(fC->Column(type));
      var->VpiEndLineNo(fC->EndLine(isSigned ? type : sign));
      var->VpiEndColumnNo(fC->EndColumn(isSigned ? type : sign));
      result = var;
      break;
    }
    case VObjectType::slIntegerAtomType_Integer: {
      integer_typespec* var = s.MakeInteger_typespec();
      var->VpiSigned(isSigned);
      var->VpiFile(fC->getFileName());
      var->VpiLineNo(fC->Line(type));
      var->VpiColumnNo(fC->Column(type));
      var->VpiEndLineNo(fC->EndLine(isSigned ? type : sign));
      var->VpiEndColumnNo(fC->EndColumn(isSigned ? type : sign));
      result = var;
      break;
    }
    case VObjectType::slIntegerAtomType_Byte: {
      byte_typespec* var = s.MakeByte_typespec();
      var->VpiSigned(isSigned);
      var->VpiFile(fC->getFileName());
      var->VpiLineNo(fC->Line(type));
      var->VpiColumnNo(fC->Column(type));
      var->VpiEndLineNo(fC->EndLine(isSigned ? type : sign));
      var->VpiEndColumnNo(fC->EndColumn(isSigned ? type : sign));
      result = var;
      break;
    }
    case VObjectType::slIntegerAtomType_LongInt: {
      long_int_typespec* var = s.MakeLong_int_typespec();
      var->VpiSigned(isSigned);
      var->VpiFile(fC->getFileName());
      var->VpiLineNo(fC->Line(type));
      var->VpiColumnNo(fC->Column(type));
      var->VpiEndLineNo(fC->EndLine(isSigned ? type : sign));
      var->VpiEndColumnNo(fC->EndColumn(isSigned ? type : sign));
      result = var;
      break;
    }
    case VObjectType::slIntegerAtomType_Shortint: {
      short_int_typespec* var = s.MakeShort_int_typespec();
      var->VpiSigned(isSigned);
      var->VpiFile(fC->getFileName());
      var->VpiLineNo(fC->Line(type));
      var->VpiColumnNo(fC->Column(type));
      var->VpiEndLineNo(fC->EndLine(isSigned ? type : sign));
      var->VpiEndColumnNo(fC->EndColumn(isSigned ? type : sign));
      result = var;
      break;
    }
    case VObjectType::slIntegerAtomType_Time: {
      time_typespec* var = s.MakeTime_typespec();
      var->VpiFile(fC->getFileName());
      var->VpiLineNo(fC->Line(type));
      var->VpiColumnNo(fC->Column(type));
      var->VpiEndLineNo(fC->EndLine(type));
      var->VpiEndColumnNo(fC->EndColumn(type));
      result = var;
      break;
    }
    case VObjectType::slIntVec_TypeBit: {
      bit_typespec* var = s.MakeBit_typespec();
      var->Ranges(ranges);
      var->VpiFile(fC->getFileName());
      var->VpiLineNo(fC->Line(type));
      var->VpiColumnNo(fC->Column(type));
      var->VpiEndLineNo(fC->EndLine(type));
      var->VpiEndColumnNo(fC->EndColumn(type));
      result = var;
      break;
    }
    case VObjectType::slNonIntType_ShortReal: {
      short_real_typespec* var = s.MakeShort_real_typespec();
      var->VpiFile(fC->getFileName());
      var->VpiLineNo(fC->Line(type));
      var->VpiColumnNo(fC->Column(type));
      var->VpiEndLineNo(fC->EndLine(type));
      var->VpiEndColumnNo(fC->EndColumn(type));
      result = var;
      break;
    }
    case VObjectType::slNonIntType_Real: {
      real_typespec* var = s.MakeReal_typespec();
      var->VpiFile(fC->getFileName());
      var->VpiLineNo(fC->Line(type));
      var->VpiColumnNo(fC->Column(type));
      var->VpiEndLineNo(fC->EndLine(type));
      var->VpiEndColumnNo(fC->EndColumn(type));
      result = var;
      break;
    }
    case VObjectType::slString_type: {
      UHDM::string_typespec* tps = s.MakeString_typespec();
      tps->VpiFile(fC->getFileName());
      tps->VpiLineNo(fC->Line(type));
      tps->VpiColumnNo(fC->Column(type));
      tps->VpiEndLineNo(fC->EndLine(type));
      tps->VpiEndColumnNo(fC->EndColumn(type));
      result = tps;
      break;
    }
    default:
      logic_typespec* var = s.MakeLogic_typespec();
      var->Ranges(ranges);
      var->VpiFile(fC->getFileName());
      var->VpiLineNo(fC->Line(type));
      var->VpiColumnNo(fC->Column(type));
      var->VpiEndLineNo(fC->EndLine(type));
      var->VpiEndColumnNo(fC->EndColumn(type));
      result = var;
      break;
  }
  return result;
}

UHDM::typespec* CompileHelper::compileTypespec(
    DesignComponent* component, const FileContent* fC, NodeId type,
    CompileDesign* compileDesign, UHDM::any* pstmt,
    SURELOG::ValuedComponentI* instance, bool reduce, bool isVariable) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::typespec* result = nullptr;
  VObjectType the_type = fC->Type(type);
  if ((the_type == VObjectType::slData_type_or_implicit) ||
      (the_type == VObjectType::slData_type)) {
    type = fC->Child(type);
    the_type = fC->Type(type);
  }
  NodeId Packed_dimension = 0;
  if (the_type == VObjectType::slPacked_dimension) {
    Packed_dimension = type;
  } else if (the_type == VObjectType::slStringConst) {
    // Class parameter or struct reference
    Packed_dimension = fC->Sibling(type);
    if (fC->Type(Packed_dimension) != slPacked_dimension) Packed_dimension = 0;
  } else {
    Packed_dimension = fC->Sibling(type);
    if (fC->Type(Packed_dimension) == slData_type_or_implicit) {
      Packed_dimension = fC->Child(Packed_dimension);
    }
  }
  bool isPacked = false;
  if (fC->Type(Packed_dimension) == slPacked_keyword) {
    Packed_dimension = fC->Sibling(Packed_dimension);
    isPacked = true;
  }
  if (fC->Type(Packed_dimension) == slStruct_union_member) {
    Packed_dimension = fC->Sibling(Packed_dimension);
  }
  if (fC->Type(Packed_dimension) == slSigning_Signed ||
      fC->Type(Packed_dimension) == slSigning_Unsigned) {
    Packed_dimension = fC->Sibling(Packed_dimension);
  }
  int size;
  VectorOfrange* ranges =
      compileRanges(component, fC, Packed_dimension, compileDesign, pstmt,
                    instance, reduce, size, false);
  switch (the_type) {
    case VObjectType::slConstant_mintypmax_expression:
    case VObjectType::slConstant_primary: {
      return compileTypespec(component, fC, fC->Child(type), compileDesign,
                             result, instance, reduce);
    }
    case VObjectType::slSystem_task: {
      UHDM::any* res = compileExpression(component, fC, type, compileDesign,
                                         nullptr, instance, reduce);
      if (res) {
        integer_typespec* var = s.MakeInteger_typespec();
        var->VpiFile(fC->getFileName());
        var->VpiLineNo(fC->Line(type));
        var->VpiColumnNo(fC->Column(type));
        var->VpiEndLineNo(fC->EndLine(type));
        var->VpiEndColumnNo(fC->EndColumn(type));
        result = var;
        if (UHDM::constant* constant = any_cast<UHDM::constant*>(res)) {
          var->VpiValue(constant->VpiValue());
        } else {
          var->Expr((expr*)res);
        }
      } else {
        unsupported_typespec* tps = s.MakeUnsupported_typespec();
        tps->VpiFile(fC->getFileName());
        tps->VpiLineNo(fC->Line(type));
        tps->VpiColumnNo(fC->Column(type));
        tps->VpiEndLineNo(fC->EndLine(type));
        tps->VpiEndColumnNo(fC->EndColumn(type));
        result = tps;
      }
      break;
    }
    case VObjectType::slEnum_base_type:
    case VObjectType::slEnum_name_declaration: {
      typespec* baseType = nullptr;
      uint64_t baseSize = 64;
      if (the_type == slEnum_base_type) {
        baseType =
            compileTypespec(component, fC, fC->Child(type), compileDesign,
                            pstmt, instance, reduce, isVariable);
        type = fC->Sibling(type);
        bool invalidValue = false;
        baseSize =
            Bits(baseType, invalidValue, component, compileDesign, instance,
                 fC->getFileName(), baseType->VpiLineNo(), reduce, true);
      }
      enum_typespec* en = s.MakeEnum_typespec();
      en->VpiFile(fC->getFileName());
      en->Base_typespec(baseType);
      VectorOfenum_const* econsts = s.MakeEnum_constVec();
      en->Enum_consts(econsts);
      NodeId enum_name_declaration = type;
      int val = 0;
      while (enum_name_declaration) {
        NodeId enumNameId = fC->Child(enum_name_declaration);
        std::string enumName = fC->SymName(enumNameId);
        NodeId enumValueId = fC->Sibling(enumNameId);
        Value* value = nullptr;
        if (enumValueId) {
          value = m_exprBuilder.evalExpr(fC, enumValueId, component);
          value->setValid();
        } else {
          value = m_exprBuilder.getValueFactory().newLValue();
          value->set(val, Value::Type::Integer, baseSize);
        }
        // the_enum->addValue(enumName, fC->Line(enumNameId), value);
        val++;
        if (component) component->setValue(enumName, value, m_exprBuilder);
        Variable* variable =
            new Variable(nullptr, fC, enumValueId, 0, enumName);
        if (component) component->addVariable(variable);

        enum_const* econst = s.MakeEnum_const();
        econst->VpiName(enumName);
        econst->VpiParent(en);
        econst->VpiFile(fC->getFileName());
        econst->VpiLineNo(fC->Line(enum_name_declaration));
        econst->VpiColumnNo(fC->Column(enum_name_declaration));
        econst->VpiEndLineNo(fC->EndLine(enum_name_declaration));
        econst->VpiEndColumnNo(fC->EndColumn(enum_name_declaration));
        econst->VpiValue(value->uhdmValue());
        if (enumValueId) {
          any* exp = compileExpression(component, fC, enumValueId,
                                       compileDesign, pstmt, nullptr);
          UHDM::ExprEval eval;
          econst->VpiDecompile(eval.prettyPrint(exp));
        } else {
          econst->VpiDecompile(value->decompiledValue());
        }
        econst->VpiSize(value->getSize());
        econsts->push_back(econst);
        enum_name_declaration = fC->Sibling(enum_name_declaration);
      }
      result = en;
      break;
    }
    case VObjectType::slInterface_identifier: {
      interface_typespec* tps = s.MakeInterface_typespec();
      NodeId Name = fC->Child(type);
      const std::string& name = fC->SymName(Name);
      tps->VpiName(name);
      tps->VpiFile(fC->getFileName());
      tps->VpiLineNo(fC->Line(type));
      tps->VpiColumnNo(fC->Column(type));
      tps->VpiEndLineNo(fC->EndLine(type));
      tps->VpiEndColumnNo(fC->EndColumn(type));
      result = tps;
      break;
    }
    case VObjectType::slSigning_Signed: {
      // Parameter implicit type is int
      if (ranges) {
        int_typespec* tps = s.MakeInt_typespec();
        tps->VpiSigned(true);
        tps->Ranges(ranges);
        result = tps;
      } else {
        int_typespec* tps = s.MakeInt_typespec();
        tps->VpiSigned(true);
        result = tps;
      }

      result->VpiFile(fC->getFileName());
      result->VpiLineNo(fC->Line(type));
      result->VpiColumnNo(fC->Column(type));
      result->VpiEndLineNo(fC->EndLine(type));
      result->VpiEndColumnNo(fC->EndColumn(type));
      break;
    }
    case VObjectType::slSigning_Unsigned: {
      // Parameter implicit type is int
      if (ranges) {
        int_typespec* tps = s.MakeInt_typespec();
        tps->Ranges(ranges);
        result = tps;
      } else {
        int_typespec* tps = s.MakeInt_typespec();
        result = tps;
      }

      result->VpiFile(fC->getFileName());
      result->VpiLineNo(fC->Line(type));
      result->VpiColumnNo(fC->Column(type));
      result->VpiEndLineNo(fC->EndLine(type));
      result->VpiEndColumnNo(fC->EndColumn(type));
      break;
    }
    case VObjectType::slPacked_dimension: {
      if (isVariable) {
        // 6.8 Variable declarations, implicit type
        logic_typespec* tps = s.MakeLogic_typespec();
        tps->Ranges(ranges);
        result = tps;
      } else {
        // Parameter implicit type is bit
        int_typespec* tps = s.MakeInt_typespec();
        tps->Ranges(ranges);
        result = tps;
      }
      result->VpiFile(fC->getFileName());
      result->VpiLineNo(fC->Line(type));
      result->VpiColumnNo(fC->Column(type));
      result->VpiEndLineNo(fC->EndLine(type));
      result->VpiEndColumnNo(fC->EndColumn(type));
      break;
    }
    case VObjectType::slExpression: {
      NodeId Primary = fC->Child(type);
      NodeId Primary_literal = fC->Child(Primary);
      NodeId Name = fC->Child(Primary_literal);
      const std::string& name = fC->SymName(Name);
      if (instance) {
        result = (typespec*)bindTypespec(name, instance, s);
      }
      break;
    }
    case VObjectType::slPrimary_literal: {
      NodeId literal = fC->Child(type);
      if (fC->Type(literal) == slStringConst) {
        const std::string& typeName = fC->SymName(literal);
        result = compileDatastructureTypespec(
            component, fC, type, compileDesign, instance, reduce, "", typeName);
      } else {
        integer_typespec* var = s.MakeInteger_typespec();
        std::string value = "INT:" + fC->SymName(literal);
        var->VpiValue(value);
        var->VpiFile(fC->getFileName());
        var->VpiLineNo(fC->Line(type));
        var->VpiColumnNo(fC->Column(type));
        var->VpiEndLineNo(fC->EndLine(type));
        var->VpiEndColumnNo(fC->EndColumn(type));
        result = var;
      }
      break;
    }
    case VObjectType::slIntVec_TypeLogic:
    case VObjectType::slNetType_Wire:
    case VObjectType::slNetType_Supply0:
    case VObjectType::slNetType_Supply1:
    case VObjectType::slNetType_Tri0:
    case VObjectType::slNetType_Tri1:
    case VObjectType::slNetType_Tri:
    case VObjectType::slNetType_TriAnd:
    case VObjectType::slNetType_TriOr:
    case VObjectType::slNetType_TriReg:
    case VObjectType::slNetType_Uwire:
    case VObjectType::slNetType_Wand:
    case VObjectType::slNetType_Wor:
    case VObjectType::slIntVec_TypeReg:
    case VObjectType::slIntegerAtomType_Int:
    case VObjectType::slIntegerAtomType_Integer:
    case VObjectType::slIntegerAtomType_Byte:
    case VObjectType::slIntegerAtomType_LongInt:
    case VObjectType::slIntegerAtomType_Shortint:
    case VObjectType::slIntegerAtomType_Time:
    case VObjectType::slIntVec_TypeBit:
    case VObjectType::slNonIntType_ShortReal:
    case VObjectType::slNonIntType_Real:
    case VObjectType::slString_type: {
      result = compileBuiltinTypespec(component, fC, type, the_type,
                                      compileDesign, ranges);
      break;
    }
    case VObjectType::slPackage_scope:
    case VObjectType::slClass_scope: {
      std::string typeName;
      NodeId class_type = fC->Child(type);
      NodeId class_name = 0;
      if (the_type == slClass_scope)
        class_name = fC->Child(class_type);
      else
        class_name = class_type;
      typeName = fC->SymName(class_name);
      std::string packageName = typeName;
      typeName += "::";
      NodeId symb_id = fC->Sibling(type);
      const std::string& name = fC->SymName(symb_id);
      typeName += name;
      Package* pack =
          compileDesign->getCompiler()->getDesign()->getPackage(packageName);
      if (pack) {
        const DataType* dtype = pack->getDataType(name);
        if (dtype == nullptr) {
          ClassDefinition* classDefn = pack->getClassDefinition(name);
          dtype = (const DataType*)classDefn;
          if (dtype) {
            class_typespec* ref = s.MakeClass_typespec();
            ref->Class_defn(classDefn->getUhdmDefinition());
            ref->VpiName(typeName);
            ref->VpiFile(fC->getFileName());
            ref->VpiLineNo(fC->Line(type));
            ref->VpiColumnNo(fC->Column(type));
            ref->VpiEndLineNo(fC->EndLine(type));
            ref->VpiEndColumnNo(fC->EndColumn(type));
            result = ref;
            break;
          }
        }
        while (dtype) {
          const TypeDef* typed = datatype_cast<const TypeDef*>(dtype);
          if (typed) {
            const DataType* dt = typed->getDataType();
            if (const Enum* en = datatype_cast<const Enum*>(dt)) {
              result = en->getTypespec();
            } else if (const Struct* st = datatype_cast<const Struct*>(dt)) {
              result = st->getTypespec();
            } else if (const Union* un = datatype_cast<const Union*>(dt)) {
              result = un->getTypespec();
            } else if (const SimpleType* sit =
                           datatype_cast<const SimpleType*>(dt)) {
              result = sit->getTypespec();
            } else if (const DummyType* sit =
                           datatype_cast<const DummyType*>(dt)) {
              result = sit->getTypespec();
            }
          }
          dtype = dtype->getDefinition();
          if (result) {
            break;
          }
        }
        if (!result) {
          UHDM::VectorOfparam_assign* param_assigns = pack->getParam_assigns();
          if (param_assigns) {
            for (param_assign* param : *param_assigns) {
              const std::string& param_name = param->Lhs()->VpiName();
              if (param_name == name) {
                const any* rhs = param->Rhs();
                if (const expr* exp = any_cast<const expr*>(rhs)) {
                  UHDM::int_typespec* its = s.MakeInt_typespec();
                  its->VpiValue(exp->VpiValue());
                  result = its;
                } else {
                  result = (UHDM::typespec*)rhs;
                }
                break;
              }
            }
          }
        }
      }
      if (result == nullptr) {
        unsupported_typespec* ref = s.MakeUnsupported_typespec();
        ref->VpiName(typeName);
        ref->VpiFile(fC->getFileName());
        ref->VpiLineNo(fC->Line(type));
        ref->VpiColumnNo(fC->Column(type));
        ref->VpiEndLineNo(fC->EndLine(type));
        ref->VpiEndColumnNo(fC->EndColumn(type));
        result = ref;
      }
      break;
    }
    case VObjectType::slStruct_union: {
      NodeId struct_or_union = fC->Child(type);
      VObjectType struct_or_union_type = fC->Type(struct_or_union);
      VectorOftypespec_member* members = s.MakeTypespec_memberVec();

      NodeId struct_or_union_member = fC->Sibling(type);
      if (fC->Type(struct_or_union_member) == VObjectType::slPacked_keyword) {
        struct_or_union_member = fC->Sibling(struct_or_union_member);
        isPacked = true;
      }

      if (struct_or_union_type == VObjectType::slStruct_keyword) {
        struct_typespec* ts = s.MakeStruct_typespec();
        ts->VpiPacked(isPacked);
        ts->Members(members);
        result = ts;
      } else {
        union_typespec* ts = s.MakeUnion_typespec();
        ts->VpiPacked(isPacked);
        ts->Members(members);
        result = ts;
      }
      result->VpiFile(fC->getFileName());
      result->VpiLineNo(fC->Line(type));
      result->VpiColumnNo(fC->Column(type));
      result->VpiEndLineNo(fC->EndLine(type));
      result->VpiEndColumnNo(fC->EndColumn(type));

      if (ranges) {
        if (isPacked) {
          packed_array_typespec* pats = s.MakePacked_array_typespec();
          pats->Elem_typespec(result);
          pats->Ranges(ranges);
          result = pats;
        } else {
          array_typespec* pats = s.MakeArray_typespec();
          pats->Elem_typespec(result);
          pats->Ranges(ranges);
          result = pats;
        }
      }

      while (struct_or_union_member) {
        NodeId Data_type_or_void = fC->Child(struct_or_union_member);
        NodeId Data_type = fC->Child(Data_type_or_void);
        NodeId List_of_variable_decl_assignments =
            fC->Sibling(Data_type_or_void);
        NodeId Variable_decl_assignment =
            fC->Child(List_of_variable_decl_assignments);
        while (Variable_decl_assignment) {
          typespec* member_ts = nullptr;
          if (Data_type) {
            member_ts = compileTypespec(component, fC, Data_type, compileDesign,
                                        result, instance, reduce);
          } else {
            void_typespec* tps = s.MakeVoid_typespec();
            tps->VpiFile(fC->getFileName());
            tps->VpiLineNo(fC->Line(Data_type_or_void));
            tps->VpiColumnNo(fC->Column(Variable_decl_assignment));
            tps->VpiEndLineNo(fC->EndLine(Data_type_or_void));
            tps->VpiEndColumnNo(fC->EndColumn(Variable_decl_assignment));
            member_ts = tps;
          }
          NodeId member_name = fC->Child(Variable_decl_assignment);
          NodeId Expression = fC->Sibling(member_name);
          const std::string& mem_name = fC->SymName(member_name);
          typespec_member* m =
              buildTypespecMember(compileDesign, fC->getFileName(), mem_name,
                                  "", fC->Line(Variable_decl_assignment),
                                  fC->Column(Variable_decl_assignment),
                                  fC->EndLine(Variable_decl_assignment),
                                  fC->EndColumn(Variable_decl_assignment));
          m->VpiRefFile(fC->getFileName().string());
          m->VpiRefLineNo(fC->Line(Data_type));
          m->VpiRefColumnNo(fC->Column(Data_type));
          m->VpiRefEndLineNo(fC->EndLine(Data_type));
          m->VpiRefEndColumnNo(fC->EndColumn(Data_type));
          m->VpiParent(result);
          m->Typespec(member_ts);
          if (Expression && (fC->Type(Expression) != slVariable_dimension)) {
            any* ex =
                compileExpression(component, fC, Expression, compileDesign,
                                  nullptr, instance, reduce, false);
            m->Default_value((expr*)ex);
          }
          if (member_ts &&
              (member_ts->UhdmType() == uhdmunsupported_typespec)) {
            component->needLateTypedefBinding(m);
          }
          members->push_back(m);
          Variable_decl_assignment = fC->Sibling(Variable_decl_assignment);
        }
        struct_or_union_member = fC->Sibling(struct_or_union_member);
      }
      break;
    }
    case VObjectType::slSimple_type:
    case VObjectType::slPs_type_identifier:
    case VObjectType::slInteger_type: {
      return compileTypespec(component, fC, fC->Child(type), compileDesign,
                             pstmt, instance, reduce);
    }
    case VObjectType::slStringConst: {
      const std::string& typeName = fC->SymName(type);
      if (typeName == "logic") {
        logic_typespec* var = s.MakeLogic_typespec();
        var->Ranges(ranges);
        var->VpiFile(fC->getFileName());
        var->VpiLineNo(fC->Line(type));
        var->VpiColumnNo(fC->Column(type));
        var->VpiEndLineNo(fC->EndLine(type));
        var->VpiEndColumnNo(fC->EndColumn(type));
        result = var;
      } else if (typeName == "bit") {
        bit_typespec* var = s.MakeBit_typespec();
        var->Ranges(ranges);
        var->VpiFile(fC->getFileName());
        var->VpiLineNo(fC->Line(type));
        var->VpiColumnNo(fC->Column(type));
        var->VpiEndLineNo(fC->EndLine(type));
        var->VpiEndColumnNo(fC->EndColumn(type));
        result = var;
      } else if (typeName == "byte") {
        byte_typespec* var = s.MakeByte_typespec();
        var->VpiFile(fC->getFileName());
        var->VpiLineNo(fC->Line(type));
        var->VpiColumnNo(fC->Column(type));
        var->VpiEndLineNo(fC->EndLine(type));
        var->VpiEndColumnNo(fC->EndColumn(type));
        result = var;
      } else if (reduce) {
        if (any* cast_to =
                getValue(typeName, component, compileDesign, instance,
                         fC->getFileName(), fC->Line(type), nullptr, !reduce)) {
          constant* c = any_cast<constant*>(cast_to);
          if (c) {
            integer_typespec* var = s.MakeInteger_typespec();
            var->VpiValue(c->VpiValue());
            var->VpiFile(fC->getFileName());
            var->VpiLineNo(fC->Line(type));
            var->VpiColumnNo(fC->Column(type));
            var->VpiEndLineNo(fC->EndLine(type));
            var->VpiEndColumnNo(fC->EndColumn(type));
            result = var;
          } else {
            void_typespec* tps = s.MakeVoid_typespec();
            tps->VpiFile(fC->getFileName());
            tps->VpiLineNo(fC->Line(type));
            tps->VpiColumnNo(fC->Column(type));
            tps->VpiEndLineNo(fC->EndLine(type));
            tps->VpiEndColumnNo(fC->EndColumn(type));
            result = tps;
          }
        }
      }
      if (!result) {
        if (component) {
          UHDM::VectorOfparam_assign* param_assigns =
              component->getParam_assigns();
          if (param_assigns) {
            for (param_assign* param : *param_assigns) {
              const std::string& param_name = param->Lhs()->VpiName();
              if (param_name == typeName) {
                const any* rhs = param->Rhs();
                if (const expr* exp = any_cast<const expr*>(rhs)) {
                  int_typespec* its = buildIntTypespec(
                      compileDesign, param->VpiFile(), typeName,
                      exp->VpiValue(), param->VpiLineNo(), param->VpiColumnNo(),
                      param->VpiLineNo(), param->VpiColumnNo());
                  // its->VpiParent((any*) param->Lhs());
                  result = its;
                } else {
                  result = (UHDM::typespec*)rhs;
                }
                break;
              }
            }
          }
        }
        if (!result) {
          while (instance) {
            if (ModuleInstance* inst =
                    valuedcomponenti_cast<ModuleInstance*>(instance)) {
              if (inst->getNetlist()) {
                UHDM::VectorOfparam_assign* param_assigns =
                    inst->getNetlist()->param_assigns();
                if (param_assigns) {
                  for (param_assign* param : *param_assigns) {
                    const std::string& param_name = param->Lhs()->VpiName();
                    if (param_name == typeName) {
                      const any* rhs = param->Rhs();
                      if (const expr* exp = any_cast<const expr*>(rhs)) {
                        int_typespec* its = buildIntTypespec(
                            compileDesign, param->VpiFile(), typeName,
                            exp->VpiValue(), param->VpiLineNo(),
                            param->VpiColumnNo(), param->VpiLineNo(),
                            param->VpiColumnNo());
                        // its->VpiParent((any*) param->Lhs());
                        result = its;
                      } else {
                        result = (UHDM::typespec*)rhs;
                      }
                      break;
                    }
                  }
                }
              }
            }
            instance = (ValuedComponentI*)instance->getParentScope();
          }
        }
      }
      if (result == nullptr) {
        result = compileDatastructureTypespec(
            component, fC, type, compileDesign, instance, reduce, "", typeName);
        if (ranges && result) {
          UHDM_OBJECT_TYPE dstype = result->UhdmType();
          if (dstype == uhdmstruct_typespec || dstype == uhdmenum_typespec ||
              dstype == uhdmunion_typespec) {
            packed_array_typespec* pats = s.MakePacked_array_typespec();
            pats->Elem_typespec(result);
            pats->Ranges(ranges);
            result = pats;
          } else if (dstype == uhdmlogic_typespec) {
            logic_typespec* pats = s.MakeLogic_typespec();
            pats->Logic_typespec((logic_typespec*)result);
            pats->Ranges(ranges);
            result = pats;
          } else if (dstype == uhdmarray_typespec) {
            packed_array_typespec* pats = s.MakePacked_array_typespec();
            pats->Elem_typespec(result);
            pats->Ranges(ranges);
            result = pats;
          } else if (dstype == uhdmpacked_array_typespec) {
            packed_array_typespec* pats = s.MakePacked_array_typespec();
            pats->Elem_typespec(result);
            pats->Ranges(ranges);
            result = pats;
          }
        }
        if (result && (result->VpiLineNo() == 0)) {
          result->VpiFile(fC->getFileName());
          result->VpiLineNo(fC->Line(type));
          result->VpiColumnNo(fC->Column(type));
          result->VpiEndLineNo(fC->EndLine(type));
          result->VpiEndColumnNo(fC->EndColumn(type));
        }
      }
      break;
    }
    case VObjectType::slConstant_expression: {
      expr* exp =
          (expr*)compileExpression(component, fC, type, compileDesign, nullptr,
                                   instance, reduce, reduce == false);
      if (exp && exp->UhdmType() == uhdmref_obj) {
        return compileTypespec(component, fC, fC->Child(type), compileDesign,
                               result, instance, reduce);
      } else {
        integer_typespec* var = s.MakeInteger_typespec();
        if (exp->UhdmType() == uhdmconstant) {
          var->VpiValue(exp->VpiValue());
        } else {
          var->Expr(exp);
        }
        var->VpiFile(fC->getFileName());
        var->VpiLineNo(fC->Line(type));
        var->VpiColumnNo(fC->Column(type));
        var->VpiEndLineNo(fC->EndLine(type));
        var->VpiEndColumnNo(fC->EndColumn(type));
        result = var;
      }
      break;
    }
    case VObjectType::slChandle_type: {
      UHDM::chandle_typespec* tps = s.MakeChandle_typespec();
      tps->VpiFile(fC->getFileName());
      tps->VpiLineNo(fC->Line(type));
      tps->VpiColumnNo(fC->Column(type));
      tps->VpiEndLineNo(fC->EndLine(type));
      tps->VpiEndColumnNo(fC->EndColumn(type));
      result = tps;
      break;
    }
    case VObjectType::slConstant_range: {
      UHDM::logic_typespec* tps = s.MakeLogic_typespec();
      tps->VpiFile(fC->getFileName());
      tps->VpiLineNo(fC->Line(type));
      tps->VpiColumnNo(fC->Column(type));
      tps->VpiEndLineNo(fC->EndLine(type));
      tps->VpiEndColumnNo(fC->EndColumn(type));
      VectorOfrange* ranges =
          compileRanges(component, fC, type, compileDesign, pstmt, instance,
                        reduce, size, false);
      tps->Ranges(ranges);
      result = tps;
      break;
    }
    case VObjectType::slEvent_type: {
      UHDM::event_typespec* tps = s.MakeEvent_typespec();
      tps->VpiFile(fC->getFileName());
      tps->VpiLineNo(fC->Line(type));
      tps->VpiColumnNo(fC->Column(type));
      tps->VpiEndLineNo(fC->EndLine(type));
      tps->VpiEndColumnNo(fC->EndColumn(type));
      result = tps;
      break;
    }
    case VObjectType::slNonIntType_RealTime: {
      UHDM::time_typespec* tps = s.MakeTime_typespec();
      tps->VpiFile(fC->getFileName());
      tps->VpiLineNo(fC->Line(type));
      tps->VpiColumnNo(fC->Column(type));
      tps->VpiEndLineNo(fC->EndLine(type));
      tps->VpiEndColumnNo(fC->EndColumn(type));
      result = tps;
      break;
    }
    case VObjectType::slType_reference: {
      NodeId child = fC->Child(type);
      if (fC->Type(child) == slExpression) {
        expr* exp =
            (expr*)compileExpression(component, fC, child, compileDesign,
                                     nullptr, instance, reduce, reduce);
        if (exp) {
          UHDM_OBJECT_TYPE typ = exp->UhdmType();
          if (type == uhdmref_obj) {
            return compileTypespec(component, fC, child, compileDesign, result,
                                   instance, reduce);
          } else if (typ == uhdmconstant) {
            constant* c = (constant*)exp;
            int ctype = c->VpiConstType();
            if (ctype == vpiIntConst || ctype == vpiDecConst) {
              int_typespec* tps = s.MakeInt_typespec();
              tps->VpiSigned(true);
              result = tps;
            } else if (ctype == vpiUIntConst || ctype == vpiBinaryConst ||
                       ctype == vpiHexConst || ctype == vpiOctConst) {
              int_typespec* tps = s.MakeInt_typespec();
              result = tps;
            } else if (ctype == vpiRealConst) {
              real_typespec* tps = s.MakeReal_typespec();
              result = tps;
            } else if (ctype == vpiStringConst) {
              string_typespec* tps = s.MakeString_typespec();
              result = tps;
            } else if (ctype == vpiTimeConst) {
              time_typespec* tps = s.MakeTime_typespec();
              result = tps;
            }
            result->VpiFile(fC->getFileName());
            result->VpiLineNo(fC->Line(type));
            result->VpiColumnNo(fC->Column(type));
            result->VpiEndLineNo(fC->EndLine(type));
            result->VpiEndColumnNo(fC->EndColumn(type));
          }
        } else {
          ErrorContainer* errors =
              compileDesign->getCompiler()->getErrorContainer();
          SymbolTable* symbols = compileDesign->getCompiler()->getSymbolTable();
          std::string fileContent =
              FileUtils::getFileContent(fC->getFileName());
          std::string lineText =
              StringUtils::getLineInString(fileContent, fC->Line(type));
          Location loc(
              symbols->registerSymbol(fC->getFileName(type).string()),
              fC->Line(type), fC->Column(type),
              symbols->registerSymbol(std::string("<") + fC->printObject(type) +
                                      std::string("> ") + lineText));
          Error err(ErrorDefinition::UHDM_UNSUPPORTED_TYPE, loc);
          errors->addError(err);
        }
      } else {
        return compileTypespec(component, fC, child, compileDesign, result,
                               instance, reduce);
      }
      break;
    }
    default:
      if (type != 0) {
        ErrorContainer* errors =
            compileDesign->getCompiler()->getErrorContainer();
        SymbolTable* symbols = compileDesign->getCompiler()->getSymbolTable();
        std::string fileContent = FileUtils::getFileContent(fC->getFileName());
        std::string lineText =
            StringUtils::getLineInString(fileContent, fC->Line(type));
        Location loc(
            symbols->registerSymbol(fC->getFileName(type).string()),
            fC->Line(type), fC->Column(type),
            symbols->registerSymbol(std::string("<") + fC->printObject(type) +
                                    std::string("> ") + lineText));
        Error err(ErrorDefinition::UHDM_UNSUPPORTED_TYPE, loc);
        errors->addError(err);
      }
      break;
  };
  if (result && component) {
    if (!result->Instance()) {
      result->Instance(component->getUhdmInstance());
    }
  }
  return result;
}

UHDM::typespec* CompileHelper::elabTypespec(DesignComponent* component,
                                            UHDM::typespec* spec,
                                            CompileDesign* compileDesign,
                                            UHDM::any* pexpr,
                                            ValuedComponentI* instance) {
  Serializer& s = compileDesign->getSerializer();
  typespec* result = spec;
  UHDM_OBJECT_TYPE type = spec->UhdmType();
  VectorOfrange* ranges = nullptr;
  switch (type) {
    case uhdmbit_typespec: {
      bit_typespec* tps = (bit_typespec*)spec;
      ranges = tps->Ranges();
      if (ranges) {
        ElaboratorListener listener(&s);
        bit_typespec* res =
            any_cast<bit_typespec*>(UHDM::clone_tree((any*)spec, s, &listener));
        ranges = res->Ranges();
        result = res;
      }
      break;
    }
    case uhdmlogic_typespec: {
      logic_typespec* tps = (logic_typespec*)spec;
      ranges = tps->Ranges();
      if (ranges) {
        ElaboratorListener listener(&s);
        logic_typespec* res = any_cast<logic_typespec*>(
            UHDM::clone_tree((any*)spec, s, &listener));
        ranges = res->Ranges();
        result = res;
      }
      break;
    }
    case uhdmarray_typespec: {
      array_typespec* tps = (array_typespec*)spec;
      ranges = tps->Ranges();
      if (ranges) {
        ElaboratorListener listener(&s);
        array_typespec* res = any_cast<array_typespec*>(
            UHDM::clone_tree((any*)spec, s, &listener));
        ranges = res->Ranges();
        result = res;
      }
      break;
    }
    case uhdmpacked_array_typespec: {
      packed_array_typespec* tps = (packed_array_typespec*)spec;
      ranges = tps->Ranges();
      if (ranges) {
        ElaboratorListener listener(&s);
        packed_array_typespec* res = any_cast<packed_array_typespec*>(
            UHDM::clone_tree((any*)spec, s, &listener));
        ranges = res->Ranges();
        result = res;
      }
      break;
    }
    default:
      break;
  }
  if (ranges) {
    for (UHDM::range* oldRange : *ranges) {
      expr* oldLeft = (expr*)oldRange->Left_expr();
      expr* oldRight = (expr*)oldRange->Right_expr();
      bool invalidValue = false;
      expr* newLeft =
          reduceExpr(oldLeft, invalidValue, component, compileDesign, instance,
                     oldLeft->VpiFile(), oldLeft->VpiLineNo(), pexpr);
      expr* newRight =
          reduceExpr(oldRight, invalidValue, component, compileDesign, instance,
                     oldRight->VpiFile(), oldRight->VpiLineNo(), pexpr);
      if (!invalidValue) {
        oldRange->Left_expr(newLeft);
        oldRange->Right_expr(newRight);
      }
    }
  }
  return result;
}

bool CompileHelper::isOverloaded(const UHDM::any* expr,
                                 CompileDesign* compileDesign,
                                 ValuedComponentI* instance) {
  if (instance == nullptr) return false;
  ModuleInstance* inst = valuedcomponenti_cast<ModuleInstance*>(instance);
  if (inst == nullptr) return false;
  std::stack<const any*> stack;
  const UHDM::any* tmp = expr;
  stack.push(tmp);
  while (!stack.empty()) {
    tmp = stack.top();
    stack.pop();
    UHDM_OBJECT_TYPE type = tmp->UhdmType();
    switch (type) {
      case uhdmrange: {
        range* r = (range*)tmp;
        stack.push(r->Left_expr());
        stack.push(r->Right_expr());
        break;
      }
      case uhdmconstant: {
        if (const typespec* tp = ((constant*)tmp)->Typespec()) {
          stack.push(tp);
        }
        break;
      }
      case uhdmtypespec: {
        typespec* tps = (typespec*)tmp;
        if (const typespec* atps = tps->Typedef_alias()) {
          stack.push(atps);
        }
        break;
      }
      case uhdmlogic_typespec: {
        logic_typespec* tps = (logic_typespec*)tmp;
        if (tps->Ranges()) {
          for (auto op : *tps->Ranges()) {
            stack.push(op);
          }
        }
        break;
      }
      case uhdmbit_typespec: {
        bit_typespec* tps = (bit_typespec*)tmp;
        if (tps->Ranges()) {
          for (auto op : *tps->Ranges()) {
            stack.push(op);
          }
        }
        break;
      }
      case uhdmarray_typespec: {
        array_typespec* tps = (array_typespec*)tmp;
        if (tps->Ranges()) {
          for (auto op : *tps->Ranges()) {
            stack.push(op);
          }
        }
        if (const typespec* etps = tps->Elem_typespec()) {
          stack.push(etps);
        }
        break;
      }
      case uhdmpacked_array_typespec: {
        packed_array_typespec* tps = (packed_array_typespec*)tmp;
        if (tps->Ranges()) {
          for (auto op : *tps->Ranges()) {
            stack.push(op);
          }
        }
        if (const any* etps = tps->Elem_typespec()) {
          stack.push(etps);
        }
        break;
      }
      case uhdmparameter:
      case uhdmref_obj:
      case uhdmtype_parameter: {
        if (inst->isOverridenParam(tmp->VpiName())) return true;
        break;
      }
      case uhdmoperation: {
        operation* oper = (operation*)tmp;
        for (auto op : *oper->Operands()) {
          stack.push(op);
        }
        break;
      }
      default:
        break;
    }
  }
  return false;
}

}  // namespace SURELOG
