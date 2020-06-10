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
#include "DesignCompile/CompileHelper.h"
#include "CompileDesign.h"
#include "uhdm.h"
#include "expr.h"
#include "UhdmWriter.h"

using namespace SURELOG;


UHDM::any* CompileHelper::compileVariable(DesignComponent* component, FileContent* fC, NodeId variable,
                                          CompileDesign* compileDesign,
                                          UHDM::any* pstmt) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::any* result = nullptr;
  VObjectType the_type = fC->Type(variable);
  NodeId Constant_range = 0;
  if (the_type == VObjectType::slData_type) {
    variable = fC->Child(variable);
    the_type = fC->Type(variable);
  } else if (the_type == VObjectType::slConstant_range) {
    Constant_range = variable;
  }
  NodeId Packed_dimension = fC->Sibling(variable);
  VectorOfrange* ranges = nullptr;
  if (Packed_dimension && (fC->Type(Packed_dimension) == VObjectType::slPacked_dimension)) {
    Constant_range = fC->Child(Packed_dimension);
  }
  if (fC->Type(Constant_range) == VObjectType::slConstant_range) { 
    ranges = s.MakeRangeVec();
    while (Constant_range) {     
      NodeId lexpr = fC->Child(Constant_range);
      NodeId rexpr = fC->Sibling(lexpr);
      range* range = s.MakeRange();
      range->Left_expr(dynamic_cast<expr*> (compileExpression(component, fC, lexpr, compileDesign)));
      range->Right_expr(dynamic_cast<expr*> (compileExpression(component, fC, rexpr, compileDesign)));
      range->VpiFile(fC->getFileName());
      range->VpiLineNo(fC->Line(Constant_range));
      ranges->push_back(range);
      Constant_range = fC->Sibling(Constant_range);
    }
  }
  if (the_type == VObjectType::slStringConst) {
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


UHDM::typespec* CompileHelper::compileTypespec(DesignComponent* component, FileContent* fC, NodeId type, 
        CompileDesign* compileDesign, UHDM::any* pstmt, const std::string& suffixname) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::typespec* result = nullptr;
  VObjectType the_type = fC->Type(type);
  if (the_type == VObjectType::slData_type) {
    type = fC->Child(type);
    the_type = fC->Type(type);
  } 
  NodeId Packed_dimension = fC->Sibling(type);
  VectorOfrange* ranges = nullptr;
  if (Packed_dimension && (fC->Type(Packed_dimension) == VObjectType::slPacked_dimension)) {
    NodeId Constant_range = fC->Child(Packed_dimension);
    if (fC->Type(Constant_range) == VObjectType::slConstant_range) { 
      ranges = s.MakeRangeVec();
      while (Constant_range) {     
        NodeId lexpr = fC->Child(Constant_range);
        NodeId rexpr = fC->Sibling(lexpr);
        range* range = s.MakeRange();
        range->Left_expr(dynamic_cast<expr*> (compileExpression(component, fC, lexpr, compileDesign, nullptr, nullptr, true)));
        range->Right_expr(dynamic_cast<expr*> (compileExpression(component, fC, rexpr, compileDesign, nullptr, nullptr, true)));
        range->VpiFile(fC->getFileName());
        range->VpiLineNo(fC->Line(Constant_range));
        ranges->push_back(range);
        Constant_range = fC->Sibling(Constant_range);
      }
    }
  }
  switch (the_type) {
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
    case VObjectType::slClass_scope: {
      std::string typeName;
      NodeId class_type = fC->Child(type);
      NodeId class_name = fC->Child(class_type);
      typeName = fC->SymName(class_name);
      std::string packageName = typeName;
      typeName += "::";
      NodeId symb_id = fC->Sibling(type);
      std::string name = fC->SymName(symb_id);
      typeName += name;
      Package* pack = compileDesign->getCompiler()->getDesign()->getPackage(packageName);
      if (pack) {
        DataType* dtype = pack->getDataType(name);
        while (dtype) {
          TypeDef* typed = dynamic_cast<TypeDef*>(dtype);
          if (typed) {
            DataType* dt = typed->getDataType();
            Enum* en = dynamic_cast<Enum*>(dt);
            if (en) {
              result = en->getTypespec();
            }
            Struct* st = dynamic_cast<Struct*>(dt);
            if (st) {
              result = st->getTypespec();
            }
            Union* un = dynamic_cast<Union*>(dt);
            if (un) {
              result = un->getTypespec();
            }
            SimpleType* sit = dynamic_cast<SimpleType*>(dt);
            if (sit) {
              result = sit->getTypespec();
            }
          }
          dtype = dtype->getDefinition();
          if (result)
            break;
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
          typespec* member_ts = compileTypespec(component, fC, Data_type, compileDesign, result);
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
    case VObjectType::slPs_type_identifier: {
      return compileTypespec(component, fC, fC->Child(type), compileDesign, pstmt);
    }
    case VObjectType::slStringConst: {
      const std::string& typeName = fC->SymName(type);
      if (component) {
        DataType* dt = component->getDataType(typeName);
        while (dt) {
          Struct* st = dynamic_cast<Struct*>(dt);
          if (st) {
            result = st->getTypespec();
            if (suffixname != "") {
              struct_typespec* tpss = (struct_typespec*)result;
              for (typespec_member* memb : *tpss->Members()) {
                if (memb->VpiName() == suffixname) {
                  result = (UHDM::typespec*) memb->Typespec();
                  break;
                }
              }
            }
            break;
          }
          Enum* en = dynamic_cast<Enum*>(dt);
          if (en) {
            result = en->getTypespec();
            break;
          }
          Union* un = dynamic_cast<Union*>(dt);
          if (un) {
            result = un->getTypespec();
            break;
          }
          SimpleType* sit = dynamic_cast<SimpleType*>(dt);
          if (sit) {
            result = sit->getTypespec();
            break;
          }
          dt = dt->getDefinition();
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
      break;
    }
    default:
      break;
  };
  return result;
}
