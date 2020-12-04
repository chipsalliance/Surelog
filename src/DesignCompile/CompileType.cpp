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
#include <iostream>
#include "Expression/Value.h"
#include "Expression/ExprBuilder.h"
#include "Design/Enum.h"
#include "Design/Struct.h"
#include "Design/Union.h"
#include "Design/SimpleType.h"
#include "Design/Function.h"
#include "Testbench/Property.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/ParseFile.h"
#include "SourceCompile/Compiler.h"
#include "Design/Design.h"
#include "Design/Parameter.h"
#include "DesignCompile/CompileHelper.h"
#include "Testbench/ClassDefinition.h"
#include "CompileDesign.h"
#include "Utils/FileUtils.h"
#include "Utils/StringUtils.h"
#include "uhdm.h"
#include "clone_tree.h"
#include "ElaboratorListener.h"
#include "expr.h"
#include "UhdmWriter.h"

using namespace SURELOG;
using namespace UHDM;

UHDM::any* CompileHelper::compileVariable(
  DesignComponent* component, const FileContent* fC, NodeId variable,
  CompileDesign* compileDesign,
  UHDM::any* pstmt, SURELOG::ValuedComponentI* instance, bool reduce) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::any* result = nullptr;
  VObjectType the_type = fC->Type(variable);
  if (the_type == VObjectType::slData_type) {
    variable = fC->Child(variable);
    the_type = fC->Type(variable);
  } else if (the_type == VObjectType::slNull_rule) {
    return nullptr;
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
  VectorOfrange* ranges = compileRanges(component, fC, Packed_dimension, compileDesign, pstmt, instance, reduce, size);
  
  if (the_type == VObjectType::slStringConst ||
      the_type == VObjectType::slChandle_type) {
    chandle_var* ref = s.MakeChandle_var();
    ref->VpiName(fC->SymName(variable));
    ref->VpiFile(fC->getFileName());
    ref->VpiLineNo(fC->Line(variable));
    result = ref;
  } else if (the_type == VObjectType::slIntVec_TypeLogic ||
             the_type == VObjectType::slIntVec_TypeReg) {
    logic_var* var = s.MakeLogic_var();
    var->Ranges(ranges);
    var->VpiFile(fC->getFileName());
    var->VpiLineNo(fC->Line(variable));
    result = var;
  } else if (the_type == VObjectType::slIntegerAtomType_Int) {
    int_var* var = s.MakeInt_var();
    var->VpiFile(fC->getFileName());
    var->VpiLineNo(fC->Line(variable));
    result = var;
  } else if (the_type == VObjectType::slIntegerAtomType_Byte) {
    byte_var* var = s.MakeByte_var();
    var->VpiFile(fC->getFileName());
    var->VpiLineNo(fC->Line(variable));
    result = var;
  } else if (the_type == VObjectType::slIntegerAtomType_LongInt) {
    long_int_var* var = s.MakeLong_int_var();
    var->VpiFile(fC->getFileName());
    var->VpiLineNo(fC->Line(variable));
    result = var;
  } else if (the_type == VObjectType::slIntegerAtomType_Shortint) {
    short_int_var* var = s.MakeShort_int_var();
    var->VpiFile(fC->getFileName());
    var->VpiLineNo(fC->Line(variable));
    result = var;
  } else if (the_type == VObjectType::slIntegerAtomType_Time) {
    time_var* var = s.MakeTime_var();
    var->VpiFile(fC->getFileName());
    var->VpiLineNo(fC->Line(variable));
    result = var;
  } else if (the_type == VObjectType::slIntVec_TypeBit) {
    bit_var* var = s.MakeBit_var();
    var->Ranges(ranges);
    var->VpiFile(fC->getFileName());
    var->VpiLineNo(fC->Line(variable));
    result = var;
  } else if (the_type == VObjectType::slNonIntType_ShortReal) {
    short_real_var* var = s.MakeShort_real_var();
    var->VpiFile(fC->getFileName());
    var->VpiLineNo(fC->Line(variable));
    result = var;
  } else if (the_type == VObjectType::slNonIntType_Real) {
    real_var* var = s.MakeReal_var();
    var->VpiFile(fC->getFileName());
    var->VpiLineNo(fC->Line(variable));
    result = var;
  } else if (the_type == VObjectType::slClass_scope) {
    std::string typeName;
    NodeId class_type = fC->Child(variable);
    NodeId class_name = fC->Child(class_type);
    typeName = fC->SymName(class_name);
    typeName += "::";
    NodeId symb_id = fC->Sibling(variable);
    typeName += fC->SymName(symb_id);
    class_var* ref = s.MakeClass_var();
    ref->VpiName(typeName);
    ref->VpiFile(fC->getFileName());
    ref->VpiLineNo(fC->Line(variable));
    result = ref;
  } else if (the_type == VObjectType::slString_type) {
    string_var* var = s.MakeString_var();
    var->VpiFile(fC->getFileName());
    var->VpiLineNo(fC->Line(variable));
    result = var;
  } else {
    // Implicit type
    logic_var* var = s.MakeLogic_var();
    var->Ranges(ranges);
    var->VpiFile(fC->getFileName());
    var->VpiLineNo(fC->Line(variable));
    result = var;
  }
  return result;
}

const UHDM::typespec* bindTypespec(const std::string& name, SURELOG::ValuedComponentI* instance) {
  const typespec* result = nullptr;
  ModuleInstance* modInst = dynamic_cast<ModuleInstance*> (instance);
  modInst = modInst->getParent();
  if (modInst) {
    for (Parameter* param : modInst->getTypeParams()) {
      const std::string& pname = param->getName();
      if (pname == name) {
        any* uparam = param->getUhdmParam();
        if (uparam) {
          type_parameter* tparam = dynamic_cast<type_parameter*> (uparam);
          if (tparam) {
            result = tparam->Typespec();
          }
        }
        break;
      }
    }
    if (result == nullptr) {
      ModuleDefinition* mod = (ModuleDefinition* )modInst->getDefinition();
      if (mod) {
        Parameter* param = mod->getParameter(name);
        if (param) {
          any* uparam =  param->getUhdmParam();
          if (uparam) {
            type_parameter* tparam = dynamic_cast<type_parameter*> (uparam);
            if (tparam) {
              result = tparam->Typespec();
            }
          }
        }
      }
    }
  }
  return result;
}

typespec* CompileHelper::compileDatastructureTypespec(DesignComponent* component,
  const FileContent* fC,
  NodeId type,
  CompileDesign* compileDesign,
  SURELOG::ValuedComponentI* instance, bool reduce,
  const std::string& suffixname,
  const std::string& typeName) {
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
        dt = compileDesign->getCompiler()->getDesign()->getClassDefinition(typeName);
      }
      if (dt == nullptr) {
        Parameter* p = component->getParameter(typeName);
        if (p && p->getUhdmParam() && (p->getUhdmParam()->UhdmType() == uhdmtype_parameter)) 
          dt = p;
      }
    }
    TypeDef* parent_tpd = nullptr;
    while (dt) {
      if (const TypeDef* tpd = dynamic_cast<const TypeDef*>(dt)) {
        parent_tpd = (TypeDef*) tpd;
      } else if (const Struct* st = dynamic_cast<const Struct*>(dt)) {
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
      } else if (const Enum* en = dynamic_cast<const Enum*>(dt)) {
        result = en->getTypespec();
        break;
      } else if (const Union* un = dynamic_cast<const Union*>(dt)) {
        result = un->getTypespec();
        break;
      } else if (const SimpleType* sit = dynamic_cast<const SimpleType*>(dt)) {
        result = sit->getTypespec();
        if (parent_tpd && result) {
          ElaboratorListener listener(&s);
          typespec* new_result = dynamic_cast<typespec*>(UHDM::clone_tree((any*) result, s, &listener));
          if (new_result) {
            new_result->Typedef_alias(result);
            result = new_result;
          }
        }
        break;
      } else if (/*const Parameter* par = */dynamic_cast<const Parameter*>(dt)) {
        // Prevent circular definition
        return nullptr;
      } else if (const ClassDefinition* classDefn =
          dynamic_cast<const ClassDefinition*>(dt)) {
        class_typespec* ref = s.MakeClass_typespec();
        ref->Class_defn(classDefn->getUhdmDefinition());
        ref->VpiName(typeName);
        ref->VpiFile(fC->getFileName());
        ref->VpiLineNo(fC->Line(type));
        result = ref;

        const FileContent* actualFC = fC;
        NodeId param = fC->Sibling(type);
        if (parent_tpd) {
          actualFC = parent_tpd->getFileContent();
          NodeId n = parent_tpd->getDefinitionNode();
          param = actualFC->Sibling(n);
        }
        if (param && (actualFC->Type(param) != slList_of_net_decl_assignments)) {
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
          if (Ordered_parameter_assignment && (actualFC->Type(Ordered_parameter_assignment) == slOrdered_parameter_assignment)) {
            while (Ordered_parameter_assignment) {
              NodeId Param_expression = actualFC->Child(Ordered_parameter_assignment);
              NodeId Data_type = actualFC->Child(Param_expression);
              std::string fName;
              const DesignComponent::ParameterVec& formal = classDefn->getOrderedParameters();
              any* fparam = nullptr;
              if (index < formal.size()) {
                Parameter* p = formal.at(index);
                fName = p->getName();
                fparam = p->getUhdmParam();
              }
              if (actualFC->Type(Data_type) == slData_type) {
                typespec* tps =
                    compileTypespec(component, actualFC, Data_type, compileDesign,
                                    result, instance, reduce);
               

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
                any* exp =
                    compileExpression(component, actualFC, Param_expression,
                                      compileDesign, nullptr, instance, reduce);
                if (exp) {
                  if (exp->UhdmType() == uhdmref_obj) {
                    const std::string& name = ((ref_obj*)exp)->VpiName();
                    typespec* tps = compileDatastructureTypespec(
                        component, actualFC, param, compileDesign, instance, reduce,
                        "", name);
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
              Ordered_parameter_assignment =
                  actualFC->Sibling(Ordered_parameter_assignment);
              index++;
            }
          }
        }
        break;
      }

      dt = dt->getDefinition();
    }

    if (result == nullptr) {
      std::string libName = fC->getLibrary()->getName();
      Design* design = compileDesign->getCompiler()->getDesign();
      ModuleDefinition* def = design->getModuleDefinition(libName + "@" + typeName);
      if (def) {
        if (def->getType() == slInterface_declaration) {
          interface_typespec* tps = s.MakeInterface_typespec();
          tps->VpiName(typeName);
          tps->VpiFile(fC->getFileName());
          tps->VpiLineNo(fC->Line(type));
          result = tps;
          if (NodeId sub = fC->Sibling(type)) {
            const std::string& name = fC->SymName(sub);
            if (def->getModPort(name)) {
              interface_typespec* mptps = s.MakeInterface_typespec();
              mptps->VpiName(name);
              mptps->VpiFile(fC->getFileName());
              mptps->VpiLineNo(fC->Line(type));
              mptps->VpiParent(tps);
              mptps->VpiIsModPort(true);
              result = mptps;
            }
          }
        }
      }
    }

    if (result == nullptr) {
      void_typespec* tps = s.MakeVoid_typespec();
      tps->VpiName(typeName);
      tps->VpiFile(fC->getFileName());
      tps->VpiLineNo(fC->Line(type));
      result = tps;
    }
  } else {
    void_typespec* tps = s.MakeVoid_typespec();
    tps->VpiName(typeName);
    tps->VpiFile(fC->getFileName());
    tps->VpiLineNo(fC->Line(type));
    result = tps;
  }
  return result;
}

UHDM::typespec* CompileHelper::compileTypespec(
  DesignComponent* component,
  const FileContent* fC, NodeId type,
  CompileDesign* compileDesign, UHDM::any* pstmt,
  SURELOG::ValuedComponentI* instance, bool reduce,
  const std::string& suffixname) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::typespec* result = nullptr;
  VObjectType the_type = fC->Type(type);
  if ((the_type == VObjectType::slData_type_or_implicit) ||  
      (the_type == VObjectType::slData_type)) {
    type = fC->Child(type);
    the_type = fC->Type(type);
  }
  NodeId Packed_dimension = 0;
  if(the_type == VObjectType::slPacked_dimension) {
    Packed_dimension = type;
  } else if (the_type == VObjectType::slStringConst) {
    // Class parameter
  } else {
    Packed_dimension = fC->Sibling(type);
  }
  int size;
  VectorOfrange* ranges = compileRanges(component, fC, Packed_dimension, compileDesign, pstmt, instance, reduce, size);
  switch (the_type) {
    case VObjectType::slConstant_mintypmax_expression: 
    case VObjectType::slConstant_primary: {
      return compileTypespec(component, fC, fC->Child(type), compileDesign, result, instance, reduce);
    }
    case VObjectType::slSystem_task: {
      UHDM::constant* constant = dynamic_cast<UHDM::constant*> (compileExpression(component, fC, type, compileDesign, nullptr, instance, true));
      if (constant) {
        integer_typespec* var = s.MakeInteger_typespec();
        var->VpiValue(constant->VpiValue());
        var->VpiFile(fC->getFileName());
        var->VpiLineNo(fC->Line(type));
        result = var;
      } else {
        void_typespec* tps = s.MakeVoid_typespec();
        tps->VpiFile(fC->getFileName());
        tps->VpiLineNo(fC->Line(type));
        result = tps;
      }
      break;
    }
    case VObjectType::slInterface_identifier: {
      interface_typespec* tps = s.MakeInterface_typespec();
      NodeId Name = fC->Child(type);
      const std::string& name = fC->SymName(Name);
      tps->VpiName(name);
      tps->VpiFile(fC->getFileName());
      tps->VpiLineNo(fC->Line(type));
      result = tps;
      break;
    }
    case VObjectType::slPacked_dimension: {
      bit_typespec* tps = s.MakeBit_typespec();
      tps->VpiFile(fC->getFileName());
      tps->VpiLineNo(fC->Line(type));
      tps->Ranges(ranges);
      result = tps;
      break;
    }
    case VObjectType::slExpression: {
      NodeId Primary = fC->Child(type);
      NodeId Primary_literal =  fC->Child(Primary);
      NodeId Name = fC->Child(Primary_literal);
      const std::string& name = fC->SymName(Name);
      if (instance) {
        result = (typespec*) bindTypespec(name, instance);
      }
      break;
    }
    case VObjectType::slPrimary_literal: {
      NodeId literal = fC->Child(type);
      integer_typespec* var = s.MakeInteger_typespec();
      std::string value = "INT:" + fC->SymName(literal);
      var->VpiValue(value);
      var->VpiFile(fC->getFileName());
      var->VpiLineNo(fC->Line(type));
      result = var;
      break;
    }
    case VObjectType::slIntVec_TypeLogic:
    case VObjectType::slIntVec_TypeReg: {
      logic_typespec* var = s.MakeLogic_typespec();
      var->Ranges(ranges);
      var->VpiFile(fC->getFileName());
      var->VpiLineNo(fC->Line(type));
      result = var;
      break;
    }
    case VObjectType::slIntegerAtomType_Int: {
      int_typespec* var = s.MakeInt_typespec();
      var->VpiFile(fC->getFileName());
      var->VpiLineNo(fC->Line(type));
      result = var;
      break;
    }
    case VObjectType::slIntegerAtomType_Byte: {
      byte_typespec* var = s.MakeByte_typespec();
      var->VpiFile(fC->getFileName());
      var->VpiLineNo(fC->Line(type));
      result = var;
      break;
    }
    case VObjectType::slIntegerAtomType_LongInt: {
      long_int_typespec* var = s.MakeLong_int_typespec();
      var->VpiFile(fC->getFileName());
      var->VpiLineNo(fC->Line(type));
      result = var;
      break;
    }
    case VObjectType::slIntegerAtomType_Shortint: {
      short_int_typespec* var = s.MakeShort_int_typespec();
      var->VpiFile(fC->getFileName());
      var->VpiLineNo(fC->Line(type));
      result = var;
      break;
    }
    case VObjectType::slIntegerAtomType_Time: {
      time_typespec* var = s.MakeTime_typespec();
      var->VpiFile(fC->getFileName());
      var->VpiLineNo(fC->Line(type));
      result = var;
      break;
    }
    case VObjectType::slIntVec_TypeBit: {
      bit_typespec* var = s.MakeBit_typespec();
      var->Ranges(ranges);
      var->VpiFile(fC->getFileName());
      var->VpiLineNo(fC->Line(type));
      result = var;
      break;
    }
    case VObjectType::slNonIntType_ShortReal: {
      short_real_typespec* var = s.MakeShort_real_typespec();
      var->VpiFile(fC->getFileName());
      var->VpiLineNo(fC->Line(type));
      result = var;
      break;
    }
    case VObjectType::slNonIntType_Real: {
      real_typespec* var = s.MakeReal_typespec();
      var->VpiFile(fC->getFileName());
      var->VpiLineNo(fC->Line(type));
      result = var;
      break;
    }
    case VObjectType::slString_type: {
      UHDM::string_typespec* tps = s.MakeString_typespec();
      tps->VpiFile(fC->getFileName());
      tps->VpiLineNo(fC->Line(type));
      result = tps;
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
      std::string name = fC->SymName(symb_id);
      typeName += name;
      Package* pack = compileDesign->getCompiler()->getDesign()->getPackage(packageName);
      if (pack) {
        const DataType* dtype = pack->getDataType(name);
        if (dtype == nullptr) {
          ClassDefinition* classDefn = dynamic_cast<ClassDefinition*>(pack->getClassDefinition(name));
          dtype = (const DataType*)classDefn;
          if (dtype) {
            class_typespec* ref = s.MakeClass_typespec();
            ref->Class_defn(classDefn->getUhdmDefinition());
            ref->VpiName(typeName);
            ref->VpiFile(fC->getFileName());
            ref->VpiLineNo(fC->Line(type));
            result = ref;
            break;
          }
        }
        while (dtype) {
          const TypeDef* typed = dynamic_cast<const TypeDef*>(dtype);
          if (typed) {
            const DataType* dt = typed->getDataType();
            const Enum* en = dynamic_cast<const Enum*>(dt);
            if (en) {
              result = en->getTypespec();
            }
            const Struct* st = dynamic_cast<const Struct*>(dt);
            if (st) {
              result = st->getTypespec();
            }
            const Union* un = dynamic_cast<const Union*>(dt);
            if (un) {
              result = un->getTypespec();
            }
            const SimpleType* sit = dynamic_cast<const SimpleType*>(dt);
            if (sit) {
              result = sit->getTypespec();
            }
          }
          dtype = dtype->getDefinition();
          if (result)
            break;
        }
        if (!result) {
          UHDM::VectorOfparam_assign* param_assigns = pack->getParam_assigns();
          if (param_assigns) {
            for (param_assign* param : *param_assigns) {
              const std::string& param_name = param->Lhs()->VpiName();
              if (param_name == name) {
                const any* rhs = param->Rhs();
                if (const expr* exp = dynamic_cast<const expr*>(rhs)) {
                  UHDM::int_typespec* its = s.MakeInt_typespec();
                  its->VpiValue(exp->VpiValue());
                  result = its;
                } else {
                  result = (UHDM::typespec*) rhs;
                }
                break;
              }
            }
          }
        }
      }
      if (result == nullptr) {
        class_typespec* ref = s.MakeClass_typespec();
        ref->VpiName(typeName);
        ref->VpiFile(fC->getFileName());
        ref->VpiLineNo(fC->Line(type));
        result = ref;
      }
      break;
    }
    case VObjectType::slStruct_union: {
      NodeId struct_or_union = fC->Child(type);
      VObjectType struct_or_union_type = fC->Type(struct_or_union);
      VectorOftypespec_member* members = s.MakeTypespec_memberVec();

      bool packed = false;
      NodeId struct_or_union_member = fC->Sibling(type);
      if (fC->Type(struct_or_union_member) == VObjectType::slPacked_keyword) {
        struct_or_union_member = fC->Sibling(struct_or_union_member);
        packed = true;
      }

      if (struct_or_union_type == VObjectType::slStruct_keyword) {
        struct_typespec* ts = s.MakeStruct_typespec();
        ts->VpiPacked(packed);
        ts->Members(members);
        result = ts;
        ts->VpiFile(fC->getFileName());
        ts->VpiLineNo(fC->Line(type));
      } else {
        union_typespec* ts = s.MakeUnion_typespec();
        ts->VpiPacked(packed);
        ts->Members(members);
        result = ts;
        ts->VpiFile(fC->getFileName());
        ts->VpiLineNo(fC->Line(type));
      }

      while (struct_or_union_member) {
        NodeId Data_type_or_void = fC->Child(struct_or_union_member);
        NodeId Data_type = fC->Child(Data_type_or_void);
        NodeId List_of_variable_decl_assignments = fC->Sibling(Data_type_or_void);
        NodeId Variable_decl_assignment = fC->Child(List_of_variable_decl_assignments);
        while (Variable_decl_assignment) {
          typespec* member_ts = nullptr;
          if (Data_type) {
            member_ts = compileTypespec(component, fC, Data_type, compileDesign, result, instance, reduce);
          } else {
            void_typespec* tps = s.MakeVoid_typespec();
            tps->VpiFile(fC->getFileName());
            tps->VpiLineNo(fC->Line(Data_type_or_void));
            member_ts = tps;
          }
          NodeId member_name = fC->Child(Variable_decl_assignment);
          typespec_member* m = s.MakeTypespec_member();
          const std::string& mem_name = fC->SymName(member_name);
          m->VpiName(mem_name);
          m->Typespec(member_ts);
          m->VpiFile(fC->getFileName());
          m->VpiLineNo(fC->Line(member_name));
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
      return compileTypespec(component, fC, fC->Child(type), compileDesign, pstmt, instance, reduce);
    }
    case VObjectType::slStringConst: {
      const std::string& typeName = fC->SymName(type);
      result = compileDatastructureTypespec(component, fC, type, compileDesign,
                                             instance, reduce, "", typeName);
      break;
    }
    case VObjectType::slConstant_expression: {
      expr* exp = (expr*) compileExpression(component, fC, type, compileDesign, nullptr, instance, true);
      if (exp && exp->UhdmType() == uhdmref_obj) {
        return compileTypespec(component, fC, fC->Child(type), compileDesign, result, instance, reduce);
      } else {
        integer_typespec* var = s.MakeInteger_typespec();
        if (exp) {
          var->VpiValue(exp->VpiValue());
        }
        var->VpiFile(fC->getFileName());
        var->VpiLineNo(fC->Line(type));
        result = var;
      }
      break;
    }
    case VObjectType::slChandle_type: {
      result = nullptr;
      break;
    }
    case VObjectType::slSigning_Signed:
    case VObjectType::slSigning_Unsigned: {
      // Parameters... will capture the signage property elsewhere
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
            symbols->registerSymbol(fC->getFileName(type)), fC->Line(type), 0,
            symbols->registerSymbol(std::string("<") + fC->printObject(type) +
                                    std::string("> ") + lineText));
        Error err(ErrorDefinition::UHDM_UNSUPPORTED_TYPE, loc);
        errors->addError(err);
      }
      break;
  };
  return result;
}
