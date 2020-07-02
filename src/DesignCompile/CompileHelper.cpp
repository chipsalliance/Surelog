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
#include <iostream>
#include "Expression/Value.h"
#include "Expression/ExprBuilder.h"
#include "Design/Enum.h"
#include "Design/Struct.h"
#include "Design/Union.h"
#include "Design/Function.h"
#include "Testbench/Property.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/ParseFile.h"
#include "SourceCompile/Compiler.h"
#include "Design/Design.h"
#include "Design/SimpleType.h"
#include "DesignCompile/CompileHelper.h"
#include "CompileDesign.h"
#include "uhdm.h"
#include "expr.h"
#include "UhdmWriter.h"

using namespace SURELOG;

CompileHelper::~CompileHelper() {}

bool CompileHelper::importPackage(DesignComponent* scope, Design* design,
                                  const FileContent* fC, NodeId id) {
  FileCNodeId fnid(fC, id);
  scope->addObject(VObjectType::slPackage_import_item, fnid);

  NodeId nameId = fC->Child(id);
  std::string pack_name = fC->SymName(nameId);
  Package* def = design->getPackage(pack_name);
  if (def) {
    scope->addAccessPackage(def);
    auto& classSet = def->getObjects(VObjectType::slClass_declaration);
    for (unsigned int i = 0; i < classSet.size(); i++) {
      const FileContent* packageFile = classSet[i].fC;
      NodeId classDef = classSet[i].nodeId;
      std::string name = packageFile->SymName(classDef);
      std::string fullName = def->getName() + "::" + name;
      DesignComponent* comp = packageFile->getComponentDefinition(fullName);
      FileCNodeId fnid(packageFile, classDef);
      scope->addNamedObject(name, fnid, comp);
    }

    auto& typeSet = def->getDataTypeMap();
    for (auto& type : typeSet) {
      scope->insertDataType(type.first, type.second);
    }

    auto& variableSet = def->getVariables();
    for (auto& var : variableSet) {
      scope->addVariable(var.second);
      Value* val = def->getValue(var.first);
      if (val) {
        scope->setValue(var.first, val, *def->getExprBuilder());
      }
    }

  } else {
    Location loc(m_symbols->registerSymbol(fC->getFileName(id)), fC->Line(id),
                 0, m_symbols->registerSymbol(pack_name));
    Error err(ErrorDefinition::COMP_UNDEFINED_PACKAGE, loc);
    m_errors->addError(err);
  }

  return true;
}

UHDM::constant* CompileHelper::constantFromValue(Value* val, CompileDesign* compileDesign) {
  Serializer& s = compileDesign->getSerializer();
  Value::Type valueType = val->getType();
  UHDM::constant* c = nullptr;
  switch(valueType) {
    case Value::Type::Scalar: {
      c = s.MakeConstant();
      c->VpiConstType(vpiScalarVal);
      c->VpiValue(val->uhdmValue());
      c->VpiDecompile(val->decompiledValue());
      break;
    }
    case Value::Type::Binary: {
      c = s.MakeConstant();
      c->VpiConstType(vpiBinStrVal);
      c->VpiValue(val->uhdmValue());
      c->VpiDecompile(val->decompiledValue());
      break;
    }
    case Value::Type::Hexadecimal: {
      c = s.MakeConstant();
      c->VpiConstType(vpiHexStrVal);
      c->VpiValue(val->uhdmValue());
      c->VpiDecompile(val->decompiledValue());
      break;
    }
    case Value::Type::Octal: {
      c = s.MakeConstant();
      c->VpiConstType(vpiOctStrVal);
      c->VpiValue(val->uhdmValue());
      c->VpiDecompile(val->decompiledValue());
      break;
    }
    case Value::Type::Unsigned:
    case Value::Type::Integer: {
      c = s.MakeConstant();
      c->VpiConstType(vpiIntVal);
      c->VpiValue(val->uhdmValue());
      c->VpiDecompile(val->decompiledValue());
      break;
    }
    case Value::Type::Double: {
      c = s.MakeConstant();
      c->VpiConstType(vpiRealVal);
      c->VpiValue(val->uhdmValue());
      c->VpiDecompile(val->decompiledValue());
      break;
    }
    case Value::Type::String: {
      c = s.MakeConstant();
      c->VpiConstType(vpiStringVal);
      c->VpiValue(val->uhdmValue());
      c->VpiDecompile(val->decompiledValue());
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
  if (tf_port_list && (fC->Type(tf_port_list) == VObjectType::slTf_port_list)) {
    NodeId tf_port_item = fC->Child(tf_port_list);
    while (tf_port_item) {
      Value* value = NULL;
      NodeId tf_data_type_or_implicit = fC->Child(tf_port_item);
      NodeId tf_data_type = fC->Child(tf_data_type_or_implicit);
      VObjectType tf_port_direction_type = fC->Type(tf_data_type_or_implicit);
      NodeId tf_param_name = fC->Sibling(tf_data_type_or_implicit);
      if (tf_port_direction_type == VObjectType::slTfPortDir_Ref ||
          tf_port_direction_type == VObjectType::slTfPortDir_ConstRef ||
          tf_port_direction_type == VObjectType::slTfPortDir_Inp ||
          tf_port_direction_type == VObjectType::slTfPortDir_Out ||
          tf_port_direction_type == VObjectType::slTfPortDir_Inout) {
        tf_data_type = fC->Sibling(tf_data_type_or_implicit);
        tf_param_name = fC->Sibling(tf_data_type);
      } else {
        tf_port_direction_type = VObjectType::slNull_rule;
      }
      NodeId type = fC->Child(tf_data_type);
      VObjectType the_type = fC->Type(type);
      std::string typeName;
      if (the_type == VObjectType::slStringConst) {
        typeName = fC->SymName(type);
      } else if (the_type == VObjectType::slClass_scope) {
        NodeId class_type = fC->Child(type);
        NodeId class_name = fC->Child(class_type);
        typeName = fC->SymName(class_name);
        typeName += "::";
        NodeId symb_id = fC->Sibling(type);
        typeName += fC->SymName(symb_id);
      } else {
        typeName = VObject::getTypeName(the_type);
      }
      std::string name = fC->SymName(tf_param_name);
      NodeId expression = fC->Sibling(tf_param_name);
      DataType* dtype = new DataType(fC, type, typeName, fC->Type(type));

      if (expression &&
          (fC->Type(expression) != VObjectType::slVariable_dimension) &&
          (dtype->getType() != VObjectType::slStringConst)) {
        value = m_exprBuilder.evalExpr(fC, expression, parent->getParent());
      }
      NodeId range = 0;
      TfPortItem* param = new TfPortItem(parent, fC, tf_port_item, range, name,
                                         dtype, value, tf_port_direction_type);
      targetList.push_back(param);
      tf_port_item = fC->Sibling(tf_port_item);
    }
  }
  return result;
}

const DataType* CompileHelper::compileTypeDef(DesignComponent* scope, const FileContent* fC,
                                        NodeId data_declaration, CompileDesign* compileDesign) {
  DataType* newType = NULL;
  Serializer& s = compileDesign->getSerializer();
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

  if (dtype == VObjectType::slClass_keyword ||
      dtype == VObjectType::slStruct_keyword ||
      dtype == VObjectType::slUnion_keyword ||
      dtype == VObjectType::slInterface_class_keyword ||
      dtype == VObjectType::slEnum_keyword) {
    NodeId type_name = fC->Sibling(data_type);
    std::string name = fC->SymName(type_name);
    const TypeDef* prevDef = scope->getTypeDef(name);
    if (prevDef) return prevDef;
    NodeId stype = fC->Sibling(data_type);
    if (fC->Type(stype) == VObjectType::slStringConst) {
      TypeDef* newTypeDef = new TypeDef(fC, type_declaration, stype, name);
      scope->insertTypeDef(newTypeDef);
      newType = newTypeDef;
      return newType;
    }
  }

  if (dtype != VObjectType::slData_type) {
    return NULL;
  }

  const NodeId type_name = fC->Sibling(data_type);
  const std::string name = fC->SymName(type_name);
  const TypeDef* prevDef = scope->getTypeDef(name);
  if (prevDef) {
    Location loc1(m_symbols->registerSymbol(fC->getFileName(data_type)),
                  fC->Line(data_type), 0, m_symbols->registerSymbol(name));
    const FileContent* prevFile = prevDef->getFileContent();
    NodeId prevNode = prevDef->getNodeId();
    Location loc2(m_symbols->registerSymbol(prevFile->getFileName(prevNode)),
                  prevFile->Line(prevNode), 0, m_symbols->registerSymbol(name));
    Error err(ErrorDefinition::COMP_MULTIPLY_DEFINED_TYPEDEF, loc1, loc2);
    m_errors->addError(err);
  }

  VObjectType base_type = fC->Type(data_type);

  DataType* type = new DataType(fC, data_type, name, base_type);
  scope->insertDataType(name, type);

  // Enum or Struct or Union
  NodeId enum_base_type = fC->Child(data_type);
  bool enumType = false;
  bool structType = false;
  //NodeId enum_base_type_node = VObjectType::slNull_rule;
  //VObjectType enum_base_type_type = VObjectType::slNull_rule;
  NodeId enum_name_declaration = VObjectType::slNull_rule;
  if (fC->Type(enum_base_type) == VObjectType::slEnum_base_type) {
    //enum_base_type_node = fC->Child(enum_base_type);
    //enum_base_type_type = fC->Type(enum_base_type_node);
    enum_name_declaration = fC->Sibling(enum_base_type);
    enumType = true;
  } else if (fC->Type(enum_base_type) == VObjectType::slEnum_name_declaration) {
    enumType = true;
    enum_name_declaration = enum_base_type;
    enum_base_type = 0;
    //enum_base_type_type = VObjectType::slIntegerAtomType_Byte;
  } else if (fC->Type(enum_base_type) == VObjectType::slStruct_union) {
    structType = true;
    NodeId struct_or_union = fC->Child(enum_base_type);
    VObjectType struct_or_union_type = fC->Type(struct_or_union);
    TypeDef* newTypeDef = new TypeDef(fC, type_declaration, type_name, name);

    if (struct_or_union_type == VObjectType::slStruct_keyword) {
      Struct* st = new Struct(fC, type_name, enum_base_type);
      newTypeDef->setDataType(st);
      newTypeDef->setDefinition(st);
      UHDM::typespec* ts = compileTypespec(scope, fC, enum_base_type, compileDesign, nullptr, nullptr, true);
      ts->VpiName(name);
      st->setTypespec(ts);
    } else if (struct_or_union_type == VObjectType::slUnion_keyword) {
      Union* st = new Union(fC, type_name, enum_base_type);
      newTypeDef->setDataType(st);
      newTypeDef->setDefinition(st);
      UHDM::typespec* ts = compileTypespec(scope, fC, enum_base_type, compileDesign, nullptr, nullptr, true);
      ts->VpiName(name);
      st->setTypespec(ts);
    }

    DesignComponent::DataTypeMap dmap = scope->getDataTypeMap();
    DesignComponent::DataTypeMap::iterator itr = dmap.find(name);
    if (itr != dmap.end()) {
      dmap.erase(itr);
    }

    type->setDefinition(newTypeDef);
    scope->insertTypeDef(newTypeDef);
    newType = newTypeDef;
  }
  if (enumType) {
    TypeDef* newTypeDef = new TypeDef(fC, type_declaration, enum_base_type, name);
    int val = 0;
    Enum* the_enum = new Enum(fC, type_name, enum_base_type);
    newTypeDef->setDataType(the_enum);
    newTypeDef->setDefinition(the_enum);
    the_enum->setBaseTypespec(compileTypespec(scope, fC, fC->Child(enum_base_type), compileDesign, nullptr, nullptr, true));
    while (enum_name_declaration) {
      NodeId enumNameId = fC->Child(enum_name_declaration);
      std::string enumName = fC->SymName(enumNameId);
      NodeId enumValueId = fC->Sibling(enumNameId);
      Value* value = NULL;
      if (enumValueId) {
        value = m_exprBuilder.evalExpr(fC, enumValueId, NULL);
      } else {
        value = m_exprBuilder.getValueFactory().newLValue();
        value->set(val, Value::Type::Integer, 32);
      }
      the_enum->addValue(enumName, fC->Line(enumNameId), value);
      enum_name_declaration = fC->Sibling(enum_name_declaration);
      val++;
      scope->setValue(enumName, value, m_exprBuilder);
      Variable* variable = new Variable(type, fC, enumValueId, 0, enumName);
      scope->addVariable(variable);
    }

    UHDM::enum_typespec* enum_t = s.MakeEnum_typespec();
    the_enum->setTypespec(enum_t);
    enum_t->VpiName(name);
    enum_t->VpiFile(the_enum->getFileContent()->getFileName());
    enum_t->VpiLineNo(the_enum->getFileContent()->Line(the_enum->getDefinitionId()));
    // Enum basetype
    enum_t->Base_typespec(the_enum->getBaseTypespec());
    // Enum values
    VectorOfenum_const* econsts = s.MakeEnum_constVec();
    enum_t->Enum_consts(econsts);
    for (std::map<std::string, std::pair<unsigned int, Value*>>::iterator
         enum_val = the_enum->getValues().begin();
         enum_val != the_enum->getValues().end(); enum_val++) {
      enum_const* econst = s.MakeEnum_const();
      econst->VpiName((*enum_val).first);
      econst->VpiFile(the_enum->getFileContent()->getFileName());
      econst->VpiLineNo((*enum_val).second.first);
      econst->VpiValue((*enum_val).second.second->uhdmValue());
      econsts->push_back(econst);
    }

    type->setDefinition(newTypeDef);
    scope->insertTypeDef(newTypeDef);
    newType = newTypeDef;

  } else if (structType) {
  } else {
    NodeId stype = fC->Child(data_type);
    if (fC->Type(stype) == VObjectType::slStringConst) {
      TypeDef* newTypeDef = new TypeDef(fC, type_declaration, stype, name);
      type->setDefinition(newTypeDef);
      scope->insertTypeDef(newTypeDef);
      newType = newTypeDef;
    } else {
      TypeDef* newTypeDef = new TypeDef(fC, type_declaration, stype, name);
      type->setDefinition(newTypeDef);
      scope->insertTypeDef(newTypeDef);
      SimpleType* simple = new SimpleType(fC, type_name, stype);
      newTypeDef->setDataType(simple);
      newTypeDef->setDefinition(simple);
      UHDM::typespec* ts = compileTypespec(scope, fC, stype, compileDesign, nullptr, nullptr, true);
      if (ts)
        ts->VpiName(name);
      simple->setTypespec(ts);
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
      case VObjectType::slFunction_statement_or_null:
      case VObjectType::slStatement_or_null: {
        NodeId statement = fC->Child(function_statement_or_null);
        NodeId statement_item = fC->Child(statement);
        NodeId item = fC->Child(statement_item);
        VObjectType stmtType = fC->Type(item);
        switch (stmtType) {
          case VObjectType::slSubroutine_call_statement: {
            compileSubroutine_call(parent, parentStmt, fC, item);
            break;
          }
          case VObjectType::slSeq_block:
            compileSeqBlock_stmt(parent, parentStmt, fC, item);
            break;
          case VObjectType::slLoop_statement:
            compileLoop_stmt(parent, parentStmt, fC, item);
            break;
          default:  // stmtType
            break;
        }
        break;
      }
      case VObjectType::slStatement: {
        NodeId statement = function_statement_or_null;
        NodeId statement_item = fC->Child(statement);
        NodeId item = fC->Child(statement_item);
        VObjectType stmtType = fC->Type(item);
        switch (stmtType) {
          case VObjectType::slSubroutine_call_statement: {
            compileSubroutine_call(parent, parentStmt, fC, item);
            break;
          }
          case VObjectType::slSeq_block:
            compileSeqBlock_stmt(parent, parentStmt, fC, item);
            break;
          case VObjectType::slLoop_statement:
            compileLoop_stmt(parent, parentStmt, fC, item);
            break;
          default:  // stmtType
            break;
        }
        break;
      } break;
      case VObjectType::slBlock_item_declaration:
        compileScopeVariable(parent, fC, function_statement_or_null);
        break;
      case VObjectType::slSuper_dot_new: {
        NodeId list_of_arguments = fC->Sibling(function_statement_or_null);
        NodeId expression = fC->Child(list_of_arguments);
        std::vector<SubRoutineArg*> args;
        while (expression) {
          SubRoutineArg* arg = new SubRoutineArg(expression, NULL);
          args.push_back(arg);
          expression = fC->Sibling(expression);
        }
        std::vector<NodeId> var_chain;
        var_chain.push_back(function_statement_or_null);
        SubRoutineCallStmt* stmt = new SubRoutineCallStmt(
            parent, parentStmt, fC, function_statement_or_null,
            VObjectType::slSubroutine_call_statement, var_chain, "new", args,
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
  if (fC->Type(base_name) == VObjectType::slDollar_keyword) {
    // system calls
    base_name = fC->Sibling(base_name);
    next_name = base_name;
    system_call = true;
  } else if (fC->Type(base_name) == VObjectType::slImplicit_class_handle) {
    next_name = fC->Sibling(base_name);
    base_name = fC->Child(base_name);
    var_chain.push_back(base_name);
  } else if (fC->Type(base_name) == VObjectType::slClass_scope) {
    next_name = fC->Sibling(base_name);
    base_name = fC->Child(base_name);
    base_name = fC->Child(base_name);
    while (base_name) {
      VObjectType ntype = fC->Type(base_name);
      if (ntype == VObjectType::slParameter_value_assignment) {
        base_name = fC->Sibling(base_name);
      }
      if (base_name == 0) break;
      var_chain.push_back(base_name);
      base_name = fC->Sibling(base_name);
    }
    static_call = true;
  }
  while (next_name) {
    VObjectType ntype = fC->Type(next_name);
    if (ntype == VObjectType::slConstant_bit_select) {
      next_name = fC->Sibling(next_name);
    }
    if (ntype == VObjectType::slSelect) {
      next_name = fC->Sibling(next_name);
    }
    if (next_name == 0) break;
    if (ntype == VObjectType::slList_of_arguments) {
      break;
    }
    var_chain.push_back(next_name);

    next_name = fC->Sibling(next_name);
  }
  std::string funcName = fC->SymName(var_chain[var_chain.size() - 1]);
  var_chain.pop_back();

  NodeId list_of_arguments = next_name;
  NodeId expression = fC->Child(list_of_arguments);
  std::vector<SubRoutineArg*> args;
  while (expression) {
    SubRoutineArg* arg = new SubRoutineArg(expression, NULL);
    args.push_back(arg);
    expression = fC->Sibling(expression);
  }

  SubRoutineCallStmt* stmt = new SubRoutineCallStmt(
      parent, parentStmt, fC, subroutine_call,
      VObjectType::slSubroutine_call_statement, var_chain, funcName, args,
      static_call, system_call);
  parent->addStmt(stmt);
  if (parentStmt) parentStmt->addStatement(stmt);
  return true;
}

bool CompileHelper::compileSeqBlock_stmt(Scope* parent, Statement* parentStmt,
                                         const FileContent* fC, NodeId seq_block) {
  NodeId item = fC->Child(seq_block);
  std::string name = "";
  SeqBlock* block = new SeqBlock(name, parent, parentStmt, fC, seq_block);
  parent->addScope(block);
  parent->addStmt(block);
  if (parentStmt) parentStmt->addStatement(block);
  compileScopeBody(block, block, fC, item);
  return true;
}

bool CompileHelper::compileLoop_stmt(Scope* parent, Statement* parentStmt,
                                     const FileContent* fC, NodeId loop_statement) {
  NodeId loop = fC->Child(loop_statement);
  switch (fC->Type(loop)) {
    case VObjectType::slFor:
      compileForLoop_stmt(parent, parentStmt, fC, fC->Sibling(loop));
      break;
    case VObjectType::slForeach:
      compileForeachLoop_stmt(parent, parentStmt, fC, fC->Sibling(loop));
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
      VObjectType::slPs_or_hierarchical_array_identifier);
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
                                        const FileContent* fC, NodeId first_node) {
  VObjectType init_type = fC->Type(first_node);
  NodeId for_initialization = 0;
  NodeId expression = 0;
  NodeId for_step = 0;
  NodeId statement_or_null = 0;
  NodeId itr_data_type = 0;
  ForLoopStmt* stmt = NULL;
  if (init_type == VObjectType::slStatement_or_null) {
    // for ( ; ; )
    statement_or_null = first_node;
    stmt = new ForLoopStmt("", parent, parentStmt, fC, first_node,
                           VObjectType::slStatement_or_null);
  } else if (init_type == VObjectType::slFor_initialization) {
    // for ( int i = 0; xxx ; xxx )
    for_initialization = first_node;
    expression = fC->Sibling(for_initialization);
    if (fC->Type(expression) == VObjectType::slExpression)
      for_step = fC->Sibling(expression);
    else {
      for_step = expression;
      expression = 0;
    }
    if (fC->Type(for_step) == VObjectType::slFor_step)
      statement_or_null = fC->Sibling(for_step);
    else {
      statement_or_null = for_step;
      for_step = 0;
    }
    stmt = new ForLoopStmt("", parent, parentStmt, fC, for_initialization,
                           VObjectType::slFor_initialization);
    NodeId for_variable_declaration = fC->Child(for_initialization);
    if (for_variable_declaration)
      itr_data_type = fC->Child(for_variable_declaration);
    NodeId the_data_type = fC->Child(itr_data_type);
    VObjectType the_type = fC->Type(the_data_type);
    stmt->setIteratorType(the_type);
  } else if (init_type == VObjectType::slExpression) {
    // for ( ; i < 1 ; xxx )
    expression = first_node;
    for_step = fC->Sibling(expression);
    if (fC->Type(for_step) == VObjectType::slFor_step)
      statement_or_null = fC->Sibling(for_step);
    else {
      statement_or_null = for_step;
      for_step = 0;
    }
    stmt = new ForLoopStmt("", parent, parentStmt, fC, first_node,
                           VObjectType::slExpression);
  }
  parent->addStmt(stmt);
  parent->addScope(stmt);

  if (expression != 0) stmt->setConditionId(expression);

  if (itr_data_type) {
    NodeId iterator = fC->Sibling(itr_data_type);
    while (iterator) {
      NodeId expression = fC->Sibling(iterator);
      if (expression) {
        stmt->addIteratorId(iterator, expression);
        iterator = fC->Sibling(expression);
      } else {
        stmt->addIteratorId(iterator, 0);
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
    if (var_type == VObjectType::slLifetime_Static) {
      var_decl = fC->Sibling(var_decl);
      var_type = fC->Type(var_decl);
    }
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
        if (varType == VObjectType::slList_of_arguments) {
          // new ()
        } else {
          std::string varName = fC->SymName(var);

          Variable* previous = parent->getVariable(varName);
          if (previous) {
            Location loc1(m_symbols->registerSymbol(fC->getFileName(var)),
                          fC->Line(var), 0, m_symbols->registerSymbol(varName));
            const FileContent* prevFile = previous->getFileContent();
            NodeId prevNode = previous->getNodeId();
            Location loc2(
                m_symbols->registerSymbol(prevFile->getFileName(prevNode)),
                prevFile->Line(prevNode), 0,
                m_symbols->registerSymbol(varName));
            Error err(ErrorDefinition::COMP_MULTIPLY_DEFINED_VARIABLE, loc1,
                      loc2);
            m_errors->addError(err);
          }

          Variable* variable = new Variable(datatype, fC, var, range, varName);
          parent->addVariable(variable);
        }

        variable_decl_assignment = fC->Sibling(variable_decl_assignment);
      }
    } else if (var_type == VObjectType::slType_declaration) {
      // compile_type_declaration_(fC, var_decl);
    }
  }

  return true;
}

Function* CompileHelper::compileFunctionPrototype(DesignComponent* scope,
                                                  const FileContent* fC, NodeId id) {
  DataType* returnType = new DataType();
  std::string funcName;
  /*
  n<"DPI-C"> u<2> t<StringLiteral> p<15> s<3> l<3>
  n<> u<3> t<Context_keyword> p<15> s<14> l<3>
  n<> u<4> t<IntVec_TypeBit> p<5> l<3>
  n<> u<5> t<Data_type> p<6> c<4> l<3>
  n<> u<6> t<Function_data_type> p<14> c<5> s<7> l<3>
  n<SV2C_peek> u<7> t<StringConst> p<14> s<13> l<3>
  n<> u<8> t<IntegerAtomType_Int> p<9> l<3>
  n<> u<9> t<Data_type> p<10> c<8> l<3>
  n<> u<10> t<Data_type_or_implicit> p<12> c<9> s<11> l<3>
  n<x_id> u<11> t<StringConst> p<12> l<3>
  n<> u<12> t<Tf_port_item> p<13> c<10> l<3>
  n<> u<13> t<Tf_port_list> p<14> c<12> l<3>
  n<> u<14> t<Function_prototype> p<15> c<6> l<3>
  n<> u<15> t<Dpi_import_export> p<16> c<2> l<3>
   */
  VObjectType type = fC->Type(id);

  if (type == VObjectType::slDpi_import_export) {
    NodeId dpiType = fC->Child(id);
    std::string stringtype;
    //      bool context = false;
    //      bool pure = false;
    if (fC->Type(dpiType) == VObjectType::slStringLiteral) {
      stringtype = fC->SymName(dpiType);
    }
    NodeId prop = fC->Sibling(dpiType);
    if (fC->Type(prop) == VObjectType::slContext_keyword) {
      // context = true;
      prop = fC->Sibling(prop);
    }
    if (fC->Type(prop) == VObjectType::slPure_keyword) {
      // pure = true;
      prop = fC->Sibling(prop);
    }
    NodeId func_prototype = prop;
    NodeId function_data_type = fC->Child(func_prototype);
    NodeId data_type = fC->Child(function_data_type);
    NodeId type = fC->Child(data_type);
    VObjectType the_type = fC->Type(type);
    std::string typeName;
    if (the_type == VObjectType::slStringConst) {
      typeName = fC->SymName(type);
    } else if (the_type == VObjectType::slClass_scope) {
      NodeId class_type = fC->Child(type);
      NodeId class_name = fC->Child(class_type);
      typeName = fC->SymName(class_name);
      typeName += "::";
      NodeId symb_id = fC->Sibling(type);
      typeName += fC->SymName(symb_id);
    } else {
      typeName = VObject::getTypeName(the_type);
    }
    returnType->init(fC, type, typeName, fC->Type(type));
    NodeId function_name = fC->Sibling(function_data_type);
    funcName = fC->SymName(function_name);
  }

  Function* result = new Function(scope, fC, id, funcName, returnType);
  Variable* variable = new Variable(returnType, fC, id, 0, funcName);
  result->addVariable(variable);
  result->compile(*this);
  return result;
}

VObjectType getSignalType(const FileContent* fC, NodeId net_port_type, NodeId& Packed_dimension) {
  Packed_dimension = 0;
  VObjectType signal_type = VObjectType::slData_type_or_implicit;
  if (net_port_type) {
    NodeId data_type_or_implicit = fC->Child(net_port_type);
    if (fC->Type(data_type_or_implicit) == VObjectType::slNetType_Wire) {
      signal_type = VObjectType::slNetType_Wire;
      data_type_or_implicit = fC->Sibling(data_type_or_implicit);
      Packed_dimension = fC->Child(data_type_or_implicit);
    } else {
      NodeId data_type = fC->Child(data_type_or_implicit);
      if (data_type) {
        VObjectType the_type = fC->Type(data_type);
        if (the_type == VObjectType::slData_type) {
          NodeId integer_vector_type = fC->Child(data_type);
          the_type = fC->Type(integer_vector_type);
          if (the_type == VObjectType::slIntVec_TypeBit ||
              the_type == VObjectType::slIntVec_TypeLogic ||
              the_type == VObjectType::slIntVec_TypeReg) {
            signal_type = the_type;
            Packed_dimension = fC->Sibling(integer_vector_type);
          }
        } else if (the_type == VObjectType::slPacked_dimension) {
          Packed_dimension = data_type;
        }
      }
    }
  }
  return signal_type;
}

void setDirectionAndType(DesignComponent* component, const FileContent* fC,
        NodeId signal, VObjectType type,
        VObjectType signal_type, NodeId packed_dimension)
{
  ModuleDefinition* module = dynamic_cast<ModuleDefinition*> (component);
  VObjectType dir_type = slNoType;
  if (type == VObjectType::slInput_declaration)
    dir_type = slPortDir_Inp;
  else if (type == VObjectType::slOutput_declaration)
    dir_type = slPortDir_Out;
  else if (type == VObjectType::slInout_declaration)
    dir_type = slPortDir_Inout;

  if (module) {
    while (signal) {
      bool found = false;
      for (Signal* port : module->getPorts()) {
        if (port->getName() == fC->SymName(signal)) {
          found = true;
          port->setPackedDimension(packed_dimension);
          port->setDirection(dir_type);
          if (signal_type != VObjectType::slData_type_or_implicit)
            port->setType(signal_type);
          break;
        }
      }
      if (found == false) {
        Signal* sig = new Signal(fC, signal,
                  VObjectType::slData_type_or_implicit,
                  dir_type, packed_dimension);
        component->getPorts().push_back(sig);
        component->getSignals().push_back(sig);
      }
      signal = fC->Sibling(signal);
      while (fC->Type(signal) == VObjectType::slVariable_dimension) {
        signal = fC->Sibling(signal);
      }

      if (fC->Type(signal) == VObjectType::slConstant_expression) {
        signal = fC->Sibling(signal);
      }
    }
    return;
  }
  Program* program = dynamic_cast<Program*> (component);
  if (program) {
    while (signal) {
      for (auto& port : program->getPorts()) {
        if (port->getName() == fC->SymName(signal)) {
          port->setDirection(dir_type);
          if (signal_type != VObjectType::slData_type_or_implicit)
            port->setType(signal_type);
          break;
        }
      }
      signal = fC->Sibling(signal);
    }
  }
}

bool CompileHelper::compilePortDeclaration(DesignComponent* component,
        const FileContent* fC, NodeId id, VObjectType& port_direction)
{
  VObjectType type = fC->Type(id);
  switch (type) {
  case VObjectType::slPort: {
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

    NodeId Port_expression = fC->Child(id);
    if (Port_expression &&
            (fC->Type(Port_expression) == VObjectType::slPort_expression)) {
      NodeId if_type = fC->Child(Port_expression);
      if (fC->Type(if_type) == VObjectType::slPort_reference) {
        NodeId if_type_name_s = fC->Child(if_type);
        NodeId if_name = fC->Sibling(if_type);
        if (if_name) {
          NodeId if_name_s = fC->Child(if_name);
          Signal* signal = new Signal(fC, if_name_s, if_type_name_s, slNoType, 0);
          component->getPorts().push_back(signal);
        } else {
          Signal* signal = new Signal(fC, if_type_name_s,
                  VObjectType::slData_type_or_implicit,
                  port_direction, 0);
          component->getPorts().push_back(signal);
        }
      }
    }
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
      std::string interfName = fC->SymName(interfIdName);

      NodeId list_of_interface_identifiers =
              fC->Sibling(type_identifier);
      NodeId interface_identifier = fC->Child(list_of_interface_identifiers);
      while (interface_identifier) {
        NodeId identifier = fC->Child(interface_identifier);
        NodeId Unpacked_dimension = fC->Sibling(interface_identifier);
        NodeId unpackedDimension = 0;
        if (fC->Type(Unpacked_dimension) == VObjectType::slUnpacked_dimension) {
          interface_identifier = fC->Sibling(interface_identifier);
          unpackedDimension = Unpacked_dimension;
        }
        Signal* signal = new Signal(fC, identifier,interfIdName, slNoType, unpackedDimension);
        component->getSignals().push_back(signal);
        interface_identifier = fC->Sibling(interface_identifier);
        while (interface_identifier && (fC->Type(interface_identifier) == VObjectType::slUnpacked_dimension)) {
          interface_identifier = fC->Sibling(interface_identifier);
        }
      }
      break;
    }
    case VObjectType::slAttribute_instance:
      /* module dff0_test(n1);
          (* init = 32'd1 *)
          output n1; */
      subNode = fC->Sibling(subNode);
      subType = fC->Type(subNode);
    case VObjectType::slInput_declaration:
    case VObjectType::slOutput_declaration:
    case VObjectType::slInout_declaration:
    {
      /*
        n<> u<24> t<Data_type_or_implicit> p<25> l<7>
        n<> u<25> t<Net_port_type> p<28> c<24> s<27> l<7>
        n<c0> u<26> t<StringConst> p<27> l<7>
        n<> u<27> t<List_of_port_identifiers> p<28> c<26> l<7>
        n<> u<28> t<Output_declaration> p<29> c<25> l<7>
       */
      NodeId net_port_type = fC->Child(subNode);
      NodeId Packed_dimension = 0;
      VObjectType signal_type = getSignalType(fC, net_port_type, Packed_dimension);
      NodeId list_of_port_identifiers = fC->Sibling(net_port_type);
      if (fC->Type(list_of_port_identifiers) ==
              VObjectType::slPacked_dimension) {
        list_of_port_identifiers =
                fC->Sibling(list_of_port_identifiers);
      }
      NodeId signal = fC->Child(list_of_port_identifiers);
      setDirectionAndType(component, fC, signal, subType, signal_type, Packed_dimension);
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

bool CompileHelper::compileAnsiPortDeclaration(DesignComponent* component,
        const FileContent* fC, NodeId id, VObjectType& port_direction)
{
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
  if (dir_type == VObjectType::slPortDir_Out ||
          dir_type == VObjectType::slPortDir_Inp ||
          dir_type == VObjectType::slPortDir_Inout ||
          dir_type == VObjectType::slPortDir_Ref) {
    port_direction = dir_type;
    net_port_type = fC->Sibling(net_port_type);
    NodeId NetType = fC->Child(net_port_type);
    // n<> u<33> t<Packed_dimension> p<34> c<32> l<11>
    // n<> u<34> t<Data_type_or_implicit> p<35> c<33> l<11>
    NodeId packedDimension = fC->Sibling(NetType);
    NodeId specParamId = 0;
    if (packedDimension == 0) {
      packedDimension = fC->Child(NetType);
      packedDimension = fC->Child(packedDimension);
      if (fC->Type(packedDimension) == VObjectType::slClass_scope) {
        specParamId = packedDimension;
      } else if (fC->Type(packedDimension) == VObjectType::slStringConst) {
        specParamId = packedDimension;
      }
    }
    VObjectType signal_type = getSignalType(fC, net_port_type, packedDimension);
    component->getPorts().push_back(new Signal(fC, identifier, signal_type, port_direction, specParamId, packedDimension));
    component->getSignals().push_back(new Signal(fC, identifier, signal_type, port_direction, specParamId, packedDimension));
  } else if (dir_type == VObjectType::slInterface_identifier) {
    NodeId interface_port_header = net_port_header;
    NodeId interface_identifier = fC->Child(interface_port_header);
    NodeId interface_name = fC->Child(interface_identifier);
    NodeId port_name = fC->Sibling(interface_port_header);
    /*
    n<mem_if> u<10> t<StringConst> p<12> s<11> l<11>
    n<system> u<11> t<StringConst> p<12> l<11>
    n<> u<12> t<Interface_identifier> p<13> c<10> l<11>
    n<> u<13> t<Interface_port_header> p<15> c<12> s<14> l<11>
    n<sif2> u<14> t<StringConst> p<15> l<11>
    n<> u<15> t<Ansi_port_declaration> p<16> c<13> l<11>
    */
    component->getPorts().push_back(new Signal(fC, port_name, interface_name, slNoType, 0));
    //component->getSignals().push_back(new Signal(fC, port_name, interface_name));
  } else {
    NodeId data_type_or_implicit = fC->Child(net_port_type);
    NodeId data_type = fC->Child(data_type_or_implicit);
    if (data_type) {
      NodeId if_type_name_s = fC->Child(data_type);
      if (fC->Type(if_type_name_s) == VObjectType::slIntVec_TypeReg ||
              fC->Type(if_type_name_s) == VObjectType::slIntVec_TypeLogic) {
        Signal* signal = new Signal(fC, identifier, fC->Type(if_type_name_s),
                VObjectType::slNoType, 0);
        component->getPorts().push_back(signal);
        // DO NOT create signals for interfaces:
        // component->getSignals().push_back(signal);
      } else {
        component->getPorts().push_back(new Signal(fC, identifier, if_type_name_s, VObjectType::slNoType, 0));
        // DO NOT create signals for interfaces:
        // component->getSignals().push_back(signal);
      }
    } else {
      Signal* signal = new Signal(fC, identifier,
              VObjectType::slData_type_or_implicit,
              port_direction, 0);
      component->getPorts().push_back(signal);
      signal = new Signal(fC, identifier,
              VObjectType::slData_type_or_implicit,
              port_direction, 0);
      component->getSignals().push_back(signal);
    }
  }
  return true;
}

bool CompileHelper::compileNetDeclaration(DesignComponent* component,
        const FileContent* fC, NodeId id, bool interface)
{
  /*
 n<> u<17> t<NetType_Wire> p<18> l<27>
 n<> u<18> t<NetTypeOrTrireg_Net> p<22> c<17> s<21> l<27>
 n<a> u<19> t<StringConst> p<20> l<27>
 n<> u<20> t<Net_decl_assignment> p<21> c<19> l<27>
 n<> u<21> t<List_of_net_decl_assignments> p<22> c<20> l<27>
 n<> u<22> t<Net_declaration> p<23> c<18> l<27>
   */
  NodeId List_of_net_decl_assignments = 0;
  NodeId Packed_dimension = 0;
  VObjectType nettype = VObjectType::slNoType;
  VObjectType subnettype = VObjectType::slNoType;
  NodeId NetTypeOrTrireg_Net = fC->Child(id);
  NodeId NetType = fC->Child(NetTypeOrTrireg_Net);
  if (NetType == 0) {
    NetType = NetTypeOrTrireg_Net;
    nettype = fC->Type(NetType);
    if (NetType) {
      if (fC->SymName(NetType) == "logic") {
        nettype = VObjectType::slIntVec_TypeLogic;
      }
    }
    NodeId Data_type_or_implicit = fC->Sibling(NetType);
    Packed_dimension = fC->Child(Data_type_or_implicit);
    if (fC->Type(Data_type_or_implicit) == VObjectType::slData_type_or_implicit)
      List_of_net_decl_assignments = fC->Sibling(Data_type_or_implicit);
    else
      List_of_net_decl_assignments = Data_type_or_implicit;
  } else {
    nettype = fC->Type(NetType);
    NodeId net = fC->Sibling(NetTypeOrTrireg_Net);
    if (fC->Type(net) == slPacked_dimension) {
      List_of_net_decl_assignments = fC->Sibling(net);
    } else {
      List_of_net_decl_assignments = net;
    }
  }
  NodeId net_decl_assignment = fC->Child(List_of_net_decl_assignments);
  while (net_decl_assignment) {
    NodeId signal = fC->Child(net_decl_assignment);
    Signal* portRef = NULL;
    for (auto& port : component->getPorts()) {
      if (port->getName() == fC->SymName(signal)) {
        port->setType(fC->Type(NetType));
        portRef = port;
        break;
      }
    }
    NodeId Unpacked_dimension = fC->Sibling(signal);

    if (fC->Type(Packed_dimension) == slData_type) {
      NetType = fC->Child(Packed_dimension);
      subnettype = nettype;
      nettype = fC->Type(NetType);
    }

    if (nettype == slStringConst) {
      Signal* sig = new Signal(fC, signal, NetType, subnettype, Unpacked_dimension);
      if (portRef)
        portRef->setLowConn(sig);
      component->getSignals().push_back(sig);
    } else {
      Signal* sig = new Signal(fC, signal, nettype, slNoType, Packed_dimension);
      if (portRef)
        portRef->setLowConn(sig);
      component->getSignals().push_back(sig);
    }

    net_decl_assignment = fC->Sibling(net_decl_assignment);
  }
  return true;
}

bool CompileHelper::compileDataDeclaration(DesignComponent* component,
        const FileContent* fC, NodeId id,
        bool interface,
        CompileDesign* compileDesign)
{
  NodeId subNode = fC->Child(id);
  VObjectType subType = fC->Type(subNode);
  switch (subType) {
  case VObjectType::slType_declaration:
  {
    /*
      n<> u<15> t<Data_type> p<17> c<8> s<16> l<13>
      n<fsm_t> u<16> t<StringConst> p<17> l<13>
      n<> u<17> t<Type_declaration> p<18> c<15> l<13>
      n<> u<18> t<Data_declaration> p<19> c<17> l<13>
     */
    compileTypeDef(component, fC, id, compileDesign);
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
    NodeId variable_declaration = fC->Child(id);
    bool const_type = false;
    bool var_type = false;
    if (fC->Type(variable_declaration) == VObjectType::slConst_type) {
      variable_declaration = fC->Sibling(variable_declaration);
      const_type = true;
    }
    if (fC->Type(variable_declaration) == VObjectType::slVar_type) {
      variable_declaration = fC->Sibling(variable_declaration);
      var_type = true;
    }
    NodeId data_type = fC->Child(variable_declaration);
    NodeId intVec_TypeReg = fC->Child(data_type);
    NodeId packedDimension = fC->Sibling(intVec_TypeReg);
    NodeId unpackedDimension = 0;
    NodeId list_of_variable_decl_assignments = fC->Sibling(data_type);
    if (fC->Type(list_of_variable_decl_assignments) ==
            VObjectType::slPacked_dimension) {
      list_of_variable_decl_assignments =
              fC->Sibling(list_of_variable_decl_assignments);
    }
    NodeId variable_decl_assignment =
            fC->Child(list_of_variable_decl_assignments);
    while (variable_decl_assignment) {
      NodeId signal = fC->Child(variable_decl_assignment);
      Signal* portRef = NULL;
      unpackedDimension = fC->Sibling(signal);
      for (Signal* port : component->getPorts()) {
        if (port->getName() == fC->SymName(signal)) {
          port->setType(fC->Type(intVec_TypeReg));
          portRef = port;
          break;
        }
      }
      Signal* sig = new Signal(fC, signal, fC->Type(intVec_TypeReg),
              packedDimension, VObjectType::slNoType, unpackedDimension);
      if (const_type) sig->setConst();
      if (var_type) sig->setVar();
      if (portRef)
        portRef->setLowConn(sig);
      component->getSignals().push_back(sig);
      variable_decl_assignment = fC->Sibling(variable_decl_assignment);
    }
    break;
  }
  return true;
}

bool CompileHelper::compileContinuousAssignment(DesignComponent* component,
        const FileContent* fC, NodeId id,
        CompileDesign* compileDesign) {
   UHDM::Serializer& s = compileDesign->getSerializer();
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
  NodeId Strength0 = 0;
  NodeId Strength1 = 0;
  NodeId List_of_net_assignments = fC->Child(id);
  if (fC->Type(List_of_net_assignments) == VObjectType::slDrive_strength) {
    NodeId Drive_strength = List_of_net_assignments;
    Strength0 = fC->Child(Drive_strength);
    Strength1 = fC->Sibling(Strength0);
    List_of_net_assignments = fC->Sibling(List_of_net_assignments);
  }
  NodeId Net_assignment = fC->Child(List_of_net_assignments);
  while (Net_assignment) {
    NodeId Net_lvalue =  fC->Child(Net_assignment);
    // LHS
    NodeId Ps_or_hierarchical_identifier = fC->Child(Net_lvalue);
    UHDM::any* lhs_exp = compileExpression(component, fC, Ps_or_hierarchical_identifier, compileDesign);

    // RHS
    NodeId Expression = fC->Sibling(Net_lvalue);
    UHDM::any* rhs_exp = compileExpression(component, fC, Expression, compileDesign);

    UHDM::cont_assign* cassign = s.MakeCont_assign();
    if (Strength0) {
      cassign->VpiStrength0(UhdmWriter::getStrengthType(fC->Type(Strength0)));
    }
    if (Strength1) {
      cassign->VpiStrength1(UhdmWriter::getStrengthType(fC->Type(Strength1)));
    }
    cassign->Lhs((UHDM::expr*) lhs_exp);
    cassign->Rhs((UHDM::expr*) rhs_exp);
    if (lhs_exp && !lhs_exp->VpiParent())
      lhs_exp->VpiParent(cassign);
    if (rhs_exp && !rhs_exp->VpiParent())
      rhs_exp->VpiParent(cassign);
    cassign->VpiFile(fC->getFileName());
    cassign->VpiLineNo(fC->Line(id));
    if (component->getContAssigns() == nullptr) {
      component->setContAssigns(s.MakeCont_assignVec());
    }
    component->getContAssigns()->push_back(cassign);

    Net_assignment = fC->Sibling(Net_assignment);
  }
  return true;
}

  bool CompileHelper::compileInitialBlock(DesignComponent* component, const FileContent* fC,
        NodeId initial_construct, CompileDesign* compileDesign) {
    UHDM::Serializer& s = compileDesign->getSerializer();
    compileDesign->lockSerializer();
    initial* init = s.MakeInitial();
    VectorOfprocess_stmt* processes = component->getProcesses();
    if (processes == nullptr) {
      component->setProcesses(s.MakeProcess_stmtVec());
      processes = component->getProcesses();
    }
    processes->push_back(init);
    NodeId Statement_or_null = fC->Child(initial_construct);
    VectorOfany* stmts = compileStmt(component, fC, Statement_or_null, compileDesign, init);
    if (stmts)
      init->Stmt((*stmts)[0]);
    compileDesign->unlockSerializer();
    return true;
  }

UHDM::atomic_stmt* CompileHelper::compileProceduralTimingControlStmt(DesignComponent* component, const FileContent* fC,
        NodeId Procedural_timing_control_statement,
        CompileDesign* compileDesign) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  /*
  n<#100> u<70> t<IntConst> p<71> l<7>
  n<> u<71> t<Delay_control> p<72> c<70> l<7>
  n<> u<72> t<Procedural_timing_control> p<88> c<71> s<87> l<7>
  */
  NodeId Procedural_timing_control = fC->Child(Procedural_timing_control_statement);
  NodeId Delay_control = fC->Child(Procedural_timing_control);
  if (fC->Type(Delay_control) == VObjectType::slEvent_control) {
    return compileEventControlStmt(component, fC, Procedural_timing_control_statement, compileDesign);
  }
  NodeId IntConst = fC->Child(Delay_control);
  std::string value = fC->SymName(IntConst);
  UHDM::delay_control* dc = s.MakeDelay_control();
  dc->VpiDelay(value);
  NodeId Statement_or_null = fC->Sibling(Procedural_timing_control);
  VectorOfany* st = compileStmt(component, fC, Statement_or_null, compileDesign, dc);
  if (st) {
    any* stmt = (*st)[0];
    dc->Stmt(stmt);
    stmt->VpiParent(dc);
  }
  return dc;
}


bool CompileHelper::compileAlwaysBlock(DesignComponent* component, const FileContent* fC,
        NodeId id, CompileDesign* compileDesign) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  compileDesign->lockSerializer();
  always* always = s.MakeAlways();
  VectorOfprocess_stmt* processes = component->getProcesses();
  if (processes == nullptr) {
    component->setProcesses(s.MakeProcess_stmtVec());
    processes = component->getProcesses();
  }
  processes->push_back(always);
  NodeId always_keyword = fC->Child(id);
  switch (fC->Type(always_keyword)) {
    case VObjectType::slAlwaysKeywd_Always:
      always->VpiAlwaysType(vpiAlways);
      break;
    case VObjectType::slAlwaysKeywd_Comb:
      always->VpiAlwaysType(vpiAlwaysComb);
      break;
    case VObjectType::slAlwaysKeywd_FF:
      always->VpiAlwaysType(vpiAlwaysFF);
      break;
    case VObjectType::slAlwaysKeywd_Latch:
      always->VpiAlwaysType(vpiAlwaysLatch);
      break;
    default:
      break;
  }
  NodeId Statement = fC->Sibling(always_keyword);
  NodeId Statement_item = fC->Child(Statement);
  NodeId the_stmt = fC->Child(Statement_item);
  VectorOfany* stmts = compileStmt(component, fC, the_stmt, compileDesign, always);
  if (stmts) {
    any* stmt = (*stmts)[0];
    always->Stmt(stmt);
    stmt->VpiParent(always);
  }
  always->VpiFile(fC->getFileName());
  always->VpiLineNo(fC->Line(id));
  compileDesign->unlockSerializer();
  return true;
}

bool CompileHelper::compileParameterDeclaration(DesignComponent* component, const FileContent* fC, NodeId nodeId,
        CompileDesign* compileDesign, bool localParam, ValuedComponentI* instance) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  compileDesign->lockSerializer();
  NodeId Data_type_or_implicit = fC->Child(nodeId);
  UHDM::typespec* ts = compileTypespec(component, fC, fC->Child(Data_type_or_implicit), compileDesign, nullptr, instance, true);
  NodeId List_of_param_assignments = fC->Sibling(Data_type_or_implicit);
  std::vector<UHDM::any*>* parameters= component->getParameters();
  if (parameters == nullptr) {
    component->setParameters(s.MakeAnyVec());
    parameters= component->getParameters();
  }
  UHDM::VectorOfparam_assign* param_assigns= component->getParam_assigns();
  if (param_assigns == nullptr) {
    component->setParam_assigns(s.MakeParam_assignVec());
    param_assigns= component->getParam_assigns();
  }
  NodeId Param_assignment = fC->Child(List_of_param_assignments);
  while (Param_assignment) {
    NodeId name = fC->Child(Param_assignment);
    NodeId value = fC->Sibling(name);
    expr* unpacked = nullptr;
    UHDM::parameter* param = s.MakeParameter();
    param->VpiFile(fC->getFileName());
    param->VpiLineNo(fC->Line(Param_assignment));
    // Unpacked dimensions
    if (fC->Type(value) == VObjectType::slUnpacked_dimension) {
      int unpackedSize;
      std::vector<UHDM::range*>* unpackedDimensions =
            compileRanges(component, fC, value, compileDesign,
                                   param, instance, true, unpackedSize);
      param->Ranges(unpackedDimensions);
      param->VpiSize(unpackedSize);
      while (fC->Type(value) == VObjectType::slUnpacked_dimension) {
        value = fC->Sibling(value);
      }
    }
    if (localParam) {
      param->VpiLocalParam(true);
    }
    parameters->push_back(param);
    UHDM::param_assign* param_assign = s.MakeParam_assign();
    param_assign->VpiFile(fC->getFileName());
    param_assign->VpiLineNo(fC->Line(Param_assignment));
    param_assigns->push_back(param_assign);
    param->VpiName(fC->SymName(name));
    param->Typespec(ts);
    param->Expr(unpacked);
    param_assign->Lhs(param);
    param_assign->Rhs((expr*) compileExpression(component, fC, value, compileDesign, nullptr, instance, true));
    Param_assignment = fC->Sibling(Param_assignment);
  }

  compileDesign->unlockSerializer();
  return true;
}

UHDM::tf_call* CompileHelper::compileTfCall(DesignComponent* component, const FileContent* fC,
        NodeId Tf_call_stmt,
        CompileDesign* compileDesign) {
  UHDM::Serializer& s = compileDesign->getSerializer();

  NodeId dollar_or_string = fC->Child(Tf_call_stmt);
  VObjectType leaf_type = fC->Type(dollar_or_string);
  NodeId tfNameNode;
  UHDM::tf_call* call = nullptr;
  std::string name;
  if (leaf_type == slDollar_keyword) {
    // System call, AST is:
    // n<> u<28> t<Subroutine_call> p<29> c<17> l<3>
    //     n<> u<17> t<Dollar_keyword> p<28> s<18> l<3>
    //     n<display> u<18> t<StringConst> p<28> s<27> l<3>
    //     n<> u<27> t<List_of_arguments> p<28> c<22> l<3>

    tfNameNode = fC->Sibling(dollar_or_string);
    call = s.MakeSys_func_call();
    name = "$" + fC->SymName(tfNameNode);
  } else if (leaf_type == slSystem_task_names) {
    tfNameNode = dollar_or_string;
    call = s.MakeSys_func_call();
    name = fC->SymName(fC->Child(dollar_or_string));
  } else if (leaf_type == slImplicit_class_handle) {
    NodeId handle = fC->Child(dollar_or_string);
    if (fC->Type(handle) == slSuper_keyword) {
      name = "super.";
    } else if (fC->Type(handle) == slThis_keyword) {
      name = "this.";
    } else if (fC->Type(handle) == slDollar_root_keyword) {
      name = "$root.";
    } else if (fC->Type(handle) == slThis_dot_super) {
      name = "this.super.";
    }
    tfNameNode = fC->Sibling(dollar_or_string);
    call = s.MakeSys_func_call();
    name += fC->SymName(tfNameNode);
  } else {
    // User call, AST is:
    // n<> u<27> t<Subroutine_call> p<28> c<17> l<3>
    //     n<show> u<17> t<StringConst> p<27> s<26> l<3>
    //     n<> u<26> t<List_of_arguments> p<27> c<21> l<3>

    tfNameNode = dollar_or_string;
    name = fC->SymName(tfNameNode);
    NodeId Constant_bit_select = fC->Sibling(tfNameNode);
    if (fC->Type(Constant_bit_select) == slConstant_bit_select) {
      tfNameNode = fC->Sibling(Constant_bit_select);
      name += "." + fC->SymName(tfNameNode);
      // TODO: method binding
    }

    if (component && component->getTask_funcs()) {
      // Function binding
      for (UHDM::task_func* tf : *component->getTask_funcs()) {
        if (tf->VpiName() == name) {
          if (tf->UhdmType() == uhdmfunction) {
            func_call* fcall = s.MakeFunc_call();
            fcall->Function(dynamic_cast<function*>(tf));
            call = fcall;
          } else {
            task_call* tcall = s.MakeTask_call();
            tcall->Task(dynamic_cast<task*>(tf));
            call = tcall;
          }
          break;
        }
      }
    }
    if (call == nullptr)
      call = s.MakeFunc_call();
  }
  call->VpiName(name);

  NodeId argListNode = fC->Sibling(tfNameNode);
  VectorOfany *arguments = compileTfCallArguments(component, fC, argListNode, compileDesign);
  call->Tf_call_args(arguments);

  return call;
}

VectorOfany* CompileHelper::compileTfCallArguments(DesignComponent* component, const FileContent* fC,
        NodeId Arg_list_node,
        CompileDesign* compileDesign) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  VectorOfany *arguments = s.MakeAnyVec();
  NodeId argumentNode = fC->Child(Arg_list_node);
  if (fC->Type(Arg_list_node) == VObjectType::slSelect) {
    // Task or func call with no argument, not even ()
    return arguments;
  }
  while (argumentNode) {
    UHDM::any* exp = compileExpression(component, fC, argumentNode, compileDesign);
    if (exp)
      arguments->push_back(exp);
    argumentNode = fC->Sibling(argumentNode);
  }
  return arguments;
}

UHDM::assignment* CompileHelper::compileBlockingAssignment(DesignComponent* component, const FileContent* fC,
        NodeId Operator_assignment, bool blocking,
        CompileDesign* compileDesign) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  NodeId Variable_lvalue = fC->Child(Operator_assignment);
  NodeId AssignOp_Assign = fC->Sibling(Variable_lvalue);
  NodeId Hierarchical_identifier = fC->Child(Variable_lvalue);

  UHDM::expr* lhs_rf = dynamic_cast<expr*> (compileExpression(component, fC, Hierarchical_identifier, compileDesign));

  NodeId Expression = 0;
  if (fC->Type(AssignOp_Assign) == VObjectType::slExpression) {
    Expression = AssignOp_Assign;
  } else {
    Expression = fC->Sibling(AssignOp_Assign); // To be checked
  }

  UHDM::any* rhs_rf = compileExpression(component, fC, Expression, compileDesign);

  assignment* assign = s.MakeAssignment();
  assign->VpiOpType(UhdmWriter::getVpiOpType(fC->Type(AssignOp_Assign)));
  if (blocking)
    assign->VpiBlocking(true);
  assign->Lhs(lhs_rf);
  assign->Rhs(rhs_rf);
  if (lhs_rf && !lhs_rf->VpiParent())
    lhs_rf->VpiParent(assign);
  if (rhs_rf && !rhs_rf->VpiParent())
    rhs_rf->VpiParent(assign);
  return assign;
}

UHDM::array_var* CompileHelper::compileArrayVar(DesignComponent* component, const FileContent* fC, NodeId varId,
                                   CompileDesign* compileDesign,
                                   UHDM::any* pexpr,
                                   ValuedComponentI* instance) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  array_var* result = s.MakeArray_var();


  return result;
}
