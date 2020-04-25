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


UHDM::any* CompileHelper::compileDataType(FileContent* fC, NodeId type,
                                          CompileDesign* compileDesign,
                                          UHDM::any* pstmt) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::any* result = nullptr;
  VObjectType the_type = fC->Type(type);
  if (the_type == VObjectType::slData_type) {
    type = fC->Child(type);
    the_type = fC->Type(type);
  }
  NodeId Packed_dimension = fC->Sibling(type);
  VectorOfrange* ranges = nullptr;
  if (Packed_dimension) {
    NodeId Constant_range = fC->Child(Packed_dimension);
    if (fC->Type(Constant_range) == VObjectType::slConstant_range) { 
      ranges = s.MakeRangeVec();
      while (Constant_range) {     
        NodeId lexpr = fC->Child(Constant_range);
        NodeId rexpr = fC->Sibling(lexpr);
        range* range = s.MakeRange();
        range->Left_expr(dynamic_cast<expr*> (compileExpression(nullptr, fC, lexpr, compileDesign)));
        range->Right_expr(dynamic_cast<expr*> (compileExpression(nullptr, fC, rexpr, compileDesign)));
        range->VpiFile(fC->getFileName());
        range->VpiLineNo(fC->Line(Constant_range));
        ranges->push_back(range);
        Constant_range = fC->Sibling(Constant_range);
      }
    }
  }
  if (the_type == VObjectType::slStringConst) {
    ref_obj* ref = s.MakeRef_obj();
    ref->VpiName(fC->SymName(type));
    ref->VpiFile(fC->getFileName());
    ref->VpiLineNo(fC->Line(type));
    result = ref;
  } else if (the_type == VObjectType::slIntVec_TypeLogic ||
             the_type == VObjectType::slIntVec_TypeReg) {
    logic_var* var = s.MakeLogic_var();
    var->Ranges(ranges);
    var->VpiFile(fC->getFileName());
    var->VpiLineNo(fC->Line(type));
    result = var;
  } else if (the_type == VObjectType::slIntegerAtomType_Int) {
    int_var* var = s.MakeInt_var();
    var->VpiFile(fC->getFileName());
    var->VpiLineNo(fC->Line(type));
    result = var;
  } else if (the_type == VObjectType::slIntegerAtomType_Byte) {
    byte_var* var = s.MakeByte_var();
    var->VpiFile(fC->getFileName());
    var->VpiLineNo(fC->Line(type));
    result = var;
  } else if (the_type == VObjectType::slIntegerAtomType_LongInt) {
    long_int_var* var = s.MakeLong_int_var();
    var->VpiFile(fC->getFileName());
    var->VpiLineNo(fC->Line(type));
    result = var;
  } else if (the_type == VObjectType::slIntegerAtomType_Shortint) {
    short_int_var* var = s.MakeShort_int_var();
    var->VpiFile(fC->getFileName());
    var->VpiLineNo(fC->Line(type));
    result = var;
  } else if (the_type == VObjectType::slIntegerAtomType_Time) {
    time_var* var = s.MakeTime_var();
    var->VpiFile(fC->getFileName());
    var->VpiLineNo(fC->Line(type));
    result = var;
  } else if (the_type == VObjectType::slIntVec_TypeBit) {
    bit_var* var = s.MakeBit_var();
    var->Ranges(ranges);
    var->VpiFile(fC->getFileName());
    var->VpiLineNo(fC->Line(type));
    result = var;
  } else if (the_type == VObjectType::slNonIntType_ShortReal) {
    short_real_var* var = s.MakeShort_real_var();
    var->VpiFile(fC->getFileName());
    var->VpiLineNo(fC->Line(type));
    result = var;
  } else if (the_type == VObjectType::slNonIntType_Real) {
    real_var* var = s.MakeReal_var();
    var->VpiFile(fC->getFileName());
    var->VpiLineNo(fC->Line(type));
    result = var;
  } else if (the_type == VObjectType::slClass_scope) {
    std::string typeName;
    NodeId class_type = fC->Child(type);
    NodeId class_name = fC->Child(class_type);
    typeName = fC->SymName(class_name);
    typeName += "::";
    NodeId symb_id = fC->Sibling(type);
    typeName += fC->SymName(symb_id);
    ref_obj* ref = s.MakeRef_obj();
    ref->VpiName(typeName);
    ref->VpiFile(fC->getFileName());
    ref->VpiLineNo(fC->Line(type));
    result = ref;
  }
  return result;
}
