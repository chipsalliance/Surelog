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

#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Common/NodeId.h"
#include "Surelog/Common/Session.h"
#include "Surelog/Design/DataType.h"
#include "Surelog/Design/DummyType.h"
#include "Surelog/Design/Enum.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/Design/Function.h"
#include "Surelog/Design/ModuleDefinition.h"
#include "Surelog/Design/ModuleInstance.h"
#include "Surelog/Design/Netlist.h"
#include "Surelog/Design/ParamAssign.h"
#include "Surelog/Design/Parameter.h"
#include "Surelog/Design/Signal.h"
#include "Surelog/Design/SimpleType.h"
#include "Surelog/Design/Struct.h"
#include "Surelog/Design/Task.h"
#include "Surelog/Design/Union.h"
#include "Surelog/Design/ValuedComponentI.h"
#include "Surelog/DesignCompile/CompileDesign.h"
#include "Surelog/DesignCompile/CompileHelper.h"
#include "Surelog/ErrorReporting/Error.h"
#include "Surelog/ErrorReporting/ErrorDefinition.h"
#include "Surelog/ErrorReporting/Location.h"
#include "Surelog/Library/Library.h"
#include "Surelog/Package/Package.h"
#include "Surelog/SourceCompile/Compiler.h"
#include "Surelog/SourceCompile/SymbolTable.h"
#include "Surelog/SourceCompile/VObjectTypes.h"
#include "Surelog/Testbench/ClassDefinition.h"
#include "Surelog/Testbench/TypeDef.h"
#include "Surelog/Testbench/Variable.h"
#include "Surelog/Utils/StringUtils.h"

// UHDM
#include <uhdm/BaseClass.h>
#include <uhdm/ElaboratorListener.h>
#include <uhdm/ExprEval.h>
#include <uhdm/clone_tree.h>
#include <uhdm/expr.h>
#include <uhdm/uhdm.h>
#include <uhdm/uhdm_types.h>
#include <uhdm/vpi_user.h>

#include <cstdint>
#include <stack>
#include <string>
#include <string_view>
#include <vector>

namespace SURELOG {

using namespace uhdm;  // NOLINT (using a bunch of them)

Variables* CompileHelper::getSimpleVarFromTypespec(
    const FileContent* fC, NodeId declarationId, NodeId nameId,
    uhdm::Typespec* spec, std::vector<uhdm::Range*>* packedDimensions,
    CompileDesign* compileDesign) {
  uhdm::Serializer& s = compileDesign->getSerializer();
  uhdm::Variables* var = nullptr;
  uhdm::UhdmType ttps = spec->getUhdmType();
  switch (ttps) {
    case uhdm::UhdmType::IntTypespec: {
      uhdm::IntVar* int_var = s.make<uhdm::IntVar>();
      var = int_var;
      break;
    }
    case uhdm::UhdmType::IntegerTypespec: {
      uhdm::IntegerVar* integer_var = s.make<uhdm::IntegerVar>();
      var = integer_var;
      break;
    }
    case uhdm::UhdmType::LongIntTypespec: {
      uhdm::LongIntVar* int_var = s.make<uhdm::LongIntVar>();
      var = int_var;
      break;
    }
    case uhdm::UhdmType::StringTypespec: {
      uhdm::StringVar* int_var = s.make<uhdm::StringVar>();
      var = int_var;
      break;
    }
    case uhdm::UhdmType::ShortIntTypespec: {
      uhdm::ShortIntVar* int_var = s.make<uhdm::ShortIntVar>();
      var = int_var;
      break;
    }
    case uhdm::UhdmType::ByteTypespec: {
      uhdm::ByteVar* int_var = s.make<uhdm::ByteVar>();
      var = int_var;
      break;
    }
    case uhdm::UhdmType::RealTypespec: {
      uhdm::RealVar* int_var = s.make<uhdm::RealVar>();
      var = int_var;
      break;
    }
    case uhdm::UhdmType::ShortRealTypespec: {
      uhdm::ShortRealVar* int_var = s.make<uhdm::ShortRealVar>();
      var = int_var;
      break;
    }
    case uhdm::UhdmType::TimeTypespec: {
      uhdm::TimeVar* int_var = s.make<uhdm::TimeVar>();
      var = int_var;
      break;
    }
    case uhdm::UhdmType::BitTypespec: {
      uhdm::BitVar* int_var = s.make<uhdm::BitVar>();
      var = int_var;
      break;
    }
    case uhdm::UhdmType::ClassTypespec: {
      uhdm::ClassVar* int_var = s.make<uhdm::ClassVar>();
      var = int_var;
      break;
    }
    case uhdm::UhdmType::EnumTypespec: {
      uhdm::EnumVar* enumv = s.make<uhdm::EnumVar>();
      fC->populateCoreMembers(nameId, nameId, enumv);
      var = enumv;
      if (m_elaborate == Elaborate::Yes) {
        uhdm::RefTypespec* specRef = s.make<uhdm::RefTypespec>();
        specRef->setParent(enumv);
        specRef->setActual(spec);
        enumv->setTypespec(specRef);
      }
      if (packedDimensions != nullptr) {
        uhdm::PackedArrayVar* array = s.make<uhdm::PackedArrayVar>();
        array->setRanges(packedDimensions);
        for (auto r : *packedDimensions) r->setParent(array, true);
        array->getElements(true)->emplace_back(var);
        var->setParent(array);
        var = array;
      }
      break;
    }
    case uhdm::UhdmType::LogicTypespec: {
      uhdm::LogicVar* logicv = s.make<uhdm::LogicVar>();
      fC->populateCoreMembers(nameId, nameId, logicv);
      var = logicv;

      if (packedDimensions != nullptr) {
        uhdm::PackedArrayVar* array = s.make<uhdm::PackedArrayVar>();
        array->setRanges(packedDimensions);
        for (auto r : *packedDimensions) r->setParent(array, true);
        array->getElements(true)->emplace_back(var);
        var->setParent(array);
        var = array;
      }

      break;
    }
    case uhdm::UhdmType::VoidTypespec: {
      uhdm::LogicVar* logicv = s.make<uhdm::LogicVar>();
      var = logicv;
      break;
    }
    case uhdm::UhdmType::UnionTypespec: {
      uhdm::UnionVar* unionv = s.make<uhdm::UnionVar>();
      fC->populateCoreMembers(nameId, nameId, unionv);
      var = unionv;

      if (m_elaborate == Elaborate::Yes) {
        uhdm::RefTypespec* specRef = s.make<uhdm::RefTypespec>();
        specRef->setParent(var);
        specRef->setActual(spec);
        var->setTypespec(specRef);
      }
      if (packedDimensions != nullptr) {
        uhdm::PackedArrayVar* array = s.make<uhdm::PackedArrayVar>();
        for (auto pd : *packedDimensions) pd->setParent(array, true);
        array->setRanges(packedDimensions);
        array->getElements(true)->emplace_back(var);
        var->setParent(array);
        var = array;
      }
      break;
    }
    case uhdm::UhdmType::StructTypespec: {
      uhdm::StructVar* structv = s.make<uhdm::StructVar>();
      fC->populateCoreMembers(nameId, nameId, structv);
      var = structv;

      if (m_elaborate == Elaborate::Yes) {
        uhdm::RefTypespec* specRef = s.make<uhdm::RefTypespec>();
        specRef->setParent(var);
        specRef->setActual(spec);
        var->setTypespec(specRef);
      }
      if (packedDimensions != nullptr) {
        uhdm::PackedArrayVar* array = s.make<uhdm::PackedArrayVar>();
        for (auto pd : *packedDimensions) pd->setParent(array, true);
        array->setRanges(packedDimensions);
        array->getElements(true)->emplace_back(var);
        var->setParent(array);
        var = array;
      }
      break;
    }
    case uhdm::UhdmType::ArrayTypespec: {
      uhdm::ArrayTypespec* atps = (uhdm::ArrayTypespec*)spec;
      if (uhdm::RefTypespec* atps_rt = atps->getIndexTypespec()) {
        if (uhdm::Typespec* indextps = atps_rt->getActual()) {
          return getSimpleVarFromTypespec(fC, declarationId, nameId, indextps,
                                          packedDimensions, compileDesign);
        }
      } else {
        uhdm::ArrayVar* array = s.make<uhdm::ArrayVar>();
        if (m_elaborate == Elaborate::Yes) {
          uhdm::RefTypespec* tpsRef = s.make<uhdm::RefTypespec>();
          tpsRef->setParent(array);
          tpsRef->setActual(s.make<uhdm::ArrayTypespec>());
          array->setTypespec(tpsRef);
        }
        var = array;
      }
      break;
    }
    default:
      break;
  }
  if (var && (m_elaborate == Elaborate::Yes)) {
    if (var->getTypespec() == nullptr) {
      uhdm::RefTypespec* specRef = s.make<uhdm::RefTypespec>();
      specRef->setParent(var);
      var->setTypespec(specRef);
    }
    var->getTypespec()->setActual(spec);
  }
  return var;
}

uhdm::Any* CompileHelper::compileVariable(
    DesignComponent* component, const FileContent* fC, NodeId declarationId,
    NodeId nameId, CompileDesign* compileDesign, Reduce reduce,
    uhdm::Any* pstmt, SURELOG::ValuedComponentI* instance, bool muteErrors) {
  uhdm::Serializer& s = compileDesign->getSerializer();
  Design* const design = compileDesign->getCompiler()->getDesign();
  uhdm::Any* result = nullptr;
  NodeId variable = declarationId;
  VObjectType the_type = fC->Type(variable);
  if (the_type == VObjectType::paData_type ||
      the_type == VObjectType::paPs_or_hierarchical_identifier) {
    variable = fC->Child(variable);
    the_type = fC->Type(variable);
    if (the_type == VObjectType::paVIRTUAL) {
      variable = fC->Sibling(variable);
      the_type = fC->Type(variable);
    }
  } else if (the_type == VObjectType::paImplicit_class_handle) {
    NodeId Handle = fC->Child(variable);
    if (fC->Type(Handle) == VObjectType::paThis_keyword) {
      variable = fC->Sibling(variable);
      the_type = fC->Type(variable);
    }
  } else if (the_type == VObjectType::sl_INVALID_) {
    return nullptr;
  }
  if (the_type == VObjectType::paComplex_func_call) {
    variable = fC->Child(variable);
    the_type = fC->Type(variable);
  }
  NodeId Packed_dimension = variable;
  if (fC->Type(Packed_dimension) != VObjectType::paPacked_dimension)
    Packed_dimension = fC->Sibling(variable);
  if (!Packed_dimension) {
    // Implicit return value:
    // function [1:0] fct();
    if (fC->Type(variable) == VObjectType::paConstant_range) {
      Packed_dimension = variable;
    }
  }

  if (fC->Type(variable) == VObjectType::slStringConst &&
      fC->Type(Packed_dimension) == VObjectType::slStringConst) {
    uhdm::HierPath* path = s.make<uhdm::HierPath>();
    uhdm::AnyCollection* elems = path->getPathElems(true);
    std::string fullName(fC->SymName(variable));
    uhdm::RefObj* obj = s.make<uhdm::RefObj>();
    obj->setName(fullName);
    obj->setParent(path);
    elems->emplace_back(obj);
    fC->populateCoreMembers(variable, variable, obj);
    path->setFile(obj->getFile());
    while (fC->Type(Packed_dimension) == VObjectType::slStringConst) {
      uhdm::RefObj* obj = s.make<uhdm::RefObj>();
      const std::string_view name = fC->SymName(Packed_dimension);
      fullName.append(".").append(name);
      obj->setName(name);
      obj->setParent(path);
      fC->populateCoreMembers(Packed_dimension, Packed_dimension, obj);
      elems->emplace_back(obj);
      Packed_dimension = fC->Sibling(Packed_dimension);
    }
    path->setFullName(fullName);
    if (!elems->empty()) {
      path->setStartLine(elems->front()->getStartLine());
      path->setStartColumn(elems->front()->getStartColumn());
      path->setEndLine(elems->back()->getEndLine());
      path->setEndColumn(elems->back()->getEndColumn());
    }
    return path;
  }

  int32_t size;
  uhdm::RangeCollection* ranges =
      compileRanges(component, fC, Packed_dimension, compileDesign, reduce,
                    pstmt, instance, size, muteErrors);
  uhdm::Typespec* ts = nullptr;
  VObjectType decl_type = fC->Type(declarationId);
  if ((decl_type != VObjectType::paPs_or_hierarchical_identifier) &&
      (decl_type != VObjectType::paImplicit_class_handle) &&
      (decl_type != VObjectType::slStringConst)) {
    ts = compileTypespec(component, fC, declarationId, compileDesign, reduce,
                         pstmt, instance, true);
  }
  bool isSigned = true;
  const NodeId signId = fC->Sibling(variable);
  if (signId && (fC->Type(signId) == VObjectType::paSigning_Unsigned)) {
    isSigned = false;
  }
  switch (the_type) {
    case VObjectType::slStringConst:
    case VObjectType::paChandle_type: {
      const std::string_view typeName = fC->SymName(variable);

      if (const DataType* dt = component->getDataType(design, typeName)) {
        dt = dt->getActual();
        if (uhdm::Typespec* tps = dt->getTypespec()) {
          if (uhdm::Variables* var = getSimpleVarFromTypespec(
                  fC, declarationId, nameId, tps, ranges, compileDesign)) {
            var->setParent(pstmt);
            var->setName(fC->SymName(variable));
            if ((ts != nullptr) && (var != nullptr)) {
              if (var->getTypespec() == nullptr) {
                uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
                tsRef->setName(typeName);
                tsRef->setParent(var);
                var->setTypespec(tsRef);
                fC->populateCoreMembers(declarationId, declarationId, tsRef);
              }
              var->getTypespec()->setActual(ts);
            }
            result = var;
          }
        }
      }
      if (result == nullptr) {
        std::string typespecName(typeName);
        ClassDefinition* cl = design->getClassDefinition(typeName);
        if (cl == nullptr) {
          std::string scopedName = StrCat(component->getName(), "::", typeName);
          if ((cl = design->getClassDefinition(scopedName))) {
            typespecName = scopedName;
          }
        }
        if (cl == nullptr) {
          if (const DesignComponent* p =
                  valuedcomponenti_cast<const DesignComponent*>(
                      component->getParentScope())) {
            std::string scopedName = StrCat(p->getName(), "::", typeName);
            if ((cl = design->getClassDefinition(scopedName))) {
              typespecName = scopedName;
            }
          }
        }
        if (cl) {
          uhdm::ClassVar* var = s.make<uhdm::ClassVar>();
          if (ts == nullptr) {
            uhdm::ClassTypespec* tps = s.make<uhdm::ClassTypespec>();
            tps->setClassDefn(cl->getUhdmModel<uhdm::ClassDefn>());
            tps->setName(typespecName);
            tps->setParent(pstmt);
            ts = tps;
            fC->populateCoreMembers(variable, variable, tps);
          }
          uhdm::RefTypespec* tpsRef = s.make<uhdm::RefTypespec>();
          tpsRef->setName(typespecName);
          tpsRef->setParent(var);
          tpsRef->setActual(ts);
          var->setTypespec(tpsRef);
          var->setName(fC->SymName(nameId));
          fC->populateCoreMembers(variable, variable, tpsRef);
          fC->populateCoreMembers(nameId, nameId, var);
          result = var;
        }
      }
      if ((result == nullptr) && (the_type == VObjectType::slStringConst) &&
          (ts != nullptr) &&
          (ts->getUhdmType() == uhdm::UhdmType::ClassTypespec)) {
        uhdm::ClassVar* var = s.make<uhdm::ClassVar>();
        uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
        tsRef->setParent(var);
        tsRef->setActual(ts);
        tsRef->setName(ts->getName());
        var->setTypespec(tsRef);
        var->setName(fC->SymName(nameId));
        fC->populateCoreMembers(nameId, nameId, var);
        fC->populateCoreMembers(declarationId, declarationId, tsRef);
        result = var;
      }
      if (result == nullptr) {
        if (the_type == VObjectType::paChandle_type) {
          uhdm::ChandleVar* var = s.make<uhdm::ChandleVar>();
          var->setName(fC->SymName(nameId));
          fC->populateCoreMembers(nameId, nameId, var);
          if (ts) {
            uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
            tsRef->setParent(var);
            tsRef->setActual(ts);
            tsRef->setName(ts->getName());
            fC->populateCoreMembers(declarationId, declarationId, tsRef);
            var->setTypespec(tsRef);
          }
          result = var;
        } else {
          uhdm::RefVar* ref = s.make<uhdm::RefVar>();
          ref->setName(fC->SymName(nameId));
          fC->populateCoreMembers(nameId, nameId, ref);
          if (ts != nullptr) {
            uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
            fC->populateCoreMembers(declarationId, declarationId, tsRef);
            tsRef->setParent(ref);
            tsRef->setActual(ts);
            tsRef->setName(typeName);
            fC->populateCoreMembers(declarationId, declarationId, tsRef);
            ref->setTypespec(tsRef);
          }
          result = ref;
        }
      }
      break;
    }
    case VObjectType::paIntVec_TypeLogic:
    case VObjectType::paIntVec_TypeReg: {
      uhdm::LogicVar* var = s.make<uhdm::LogicVar>();
      uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
      tsRef->setParent(var);
      tsRef->setActual(ts);
      var->setTypespec(tsRef);
      var->setName(fC->SymName(nameId));
      fC->populateCoreMembers(nameId, nameId, var);
      fC->populateCoreMembers(declarationId, declarationId, tsRef);
      result = var;
      break;
    }
    case VObjectType::paIntegerAtomType_Int: {
      uhdm::IntVar* var = s.make<uhdm::IntVar>();
      uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
      tsRef->setParent(var);
      tsRef->setActual(ts);
      var->setTypespec(tsRef);
      var->setSigned(isSigned);
      var->setName(fC->SymName(nameId));
      fC->populateCoreMembers(nameId, nameId, var);
      fC->populateCoreMembers(declarationId, declarationId, tsRef);
      result = var;
      break;
    }
    case VObjectType::paIntegerAtomType_Integer: {
      uhdm::IntegerVar* var = s.make<uhdm::IntegerVar>();
      uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
      tsRef->setParent(var);
      tsRef->setActual(ts);
      var->setTypespec(tsRef);
      var->setSigned(isSigned);
      var->setName(fC->SymName(nameId));
      fC->populateCoreMembers(nameId, nameId, var);
      fC->populateCoreMembers(declarationId, declarationId, tsRef);
      result = var;
      break;
    }
    case VObjectType::paSigning_Unsigned: {
      uhdm::IntVar* var = s.make<uhdm::IntVar>();
      uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
      tsRef->setParent(var);
      tsRef->setActual(ts);
      var->setTypespec(tsRef);
      var->setSigned(isSigned);
      var->setName(fC->SymName(nameId));
      fC->populateCoreMembers(nameId, nameId, var);
      fC->populateCoreMembers(declarationId, declarationId, tsRef);
      result = var;
      break;
    }
    case VObjectType::paSigning_Signed: {
      uhdm::IntVar* var = s.make<uhdm::IntVar>();
      if (ts != nullptr) {
        uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
        tsRef->setParent(var);
        tsRef->setActual(ts);
        var->setTypespec(tsRef);
        fC->populateCoreMembers(declarationId, declarationId, tsRef);
      }
      var->setName(fC->SymName(nameId));
      fC->populateCoreMembers(nameId, nameId, var);
      var->setSigned(isSigned);
      result = var;
      break;
    }
    case VObjectType::paIntegerAtomType_Byte: {
      uhdm::ByteVar* var = s.make<uhdm::ByteVar>();
      uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
      tsRef->setParent(var);
      tsRef->setActual(ts);
      var->setTypespec(tsRef);
      var->setSigned(isSigned);
      var->setName(fC->SymName(nameId));
      fC->populateCoreMembers(nameId, nameId, var);
      fC->populateCoreMembers(declarationId, declarationId, tsRef);
      result = var;
      break;
    }
    case VObjectType::paIntegerAtomType_LongInt: {
      uhdm::LongIntVar* var = s.make<uhdm::LongIntVar>();
      uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
      tsRef->setParent(var);
      tsRef->setActual(ts);
      var->setTypespec(tsRef);
      var->setSigned(isSigned);
      var->setName(fC->SymName(nameId));
      fC->populateCoreMembers(nameId, nameId, var);
      fC->populateCoreMembers(declarationId, declarationId, tsRef);
      result = var;
      break;
    }
    case VObjectType::paIntegerAtomType_Shortint: {
      uhdm::ShortIntVar* var = s.make<uhdm::ShortIntVar>();
      uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
      tsRef->setParent(var);
      tsRef->setActual(ts);
      var->setTypespec(tsRef);
      var->setSigned(isSigned);
      var->setName(fC->SymName(nameId));
      fC->populateCoreMembers(nameId, nameId, var);
      fC->populateCoreMembers(declarationId, declarationId, tsRef);
      result = var;
      break;
    }
    case VObjectType::paIntegerAtomType_Time: {
      uhdm::TimeVar* var = s.make<uhdm::TimeVar>();
      uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
      tsRef->setParent(var);
      tsRef->setActual(ts);
      var->setTypespec(tsRef);
      var->setName(fC->SymName(nameId));
      fC->populateCoreMembers(nameId, nameId, var);
      fC->populateCoreMembers(declarationId, declarationId, tsRef);
      result = var;
      break;
    }
    case VObjectType::paIntVec_TypeBit: {
      uhdm::BitVar* var = s.make<uhdm::BitVar>();
      uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
      tsRef->setParent(var);
      tsRef->setActual(ts);
      var->setTypespec(tsRef);
      var->setName(fC->SymName(nameId));
      fC->populateCoreMembers(nameId, nameId, var);
      fC->populateCoreMembers(declarationId, declarationId, tsRef);
      result = var;
      break;
    }
    case VObjectType::paNonIntType_ShortReal: {
      uhdm::ShortRealVar* var = s.make<uhdm::ShortRealVar>();
      uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
      tsRef->setParent(var);
      tsRef->setActual(ts);
      var->setTypespec(tsRef);
      var->setName(fC->SymName(nameId));
      fC->populateCoreMembers(nameId, nameId, var);
      fC->populateCoreMembers(declarationId, declarationId, tsRef);
      result = var;
      break;
    }
    case VObjectType::paNonIntType_Real: {
      uhdm::RealVar* var = s.make<uhdm::RealVar>();
      uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
      tsRef->setParent(var);
      tsRef->setActual(ts);
      var->setTypespec(tsRef);
      var->setName(fC->SymName(nameId));
      fC->populateCoreMembers(nameId, nameId, var);
      fC->populateCoreMembers(declarationId, declarationId, tsRef);
      result = var;
      break;
    }
    case VObjectType::paClass_scope: {
      NodeId class_type = fC->Child(variable);
      NodeId class_name = fC->Child(class_type);
      const std::string_view packageName = fC->SymName(class_name);
      Design* const design = compileDesign->getCompiler()->getDesign();
      NodeId symb_id = fC->Sibling(variable);
      const std::string_view typeName = fC->SymName(symb_id);
      Package* pack = design->getPackage(packageName);
      uhdm::Variables* var = nullptr;
      if (pack) {
        const DataType* dtype = pack->getDataType(design, typeName);
        while (dtype) {
          if (uhdm::Typespec* tps = dtype->getTypespec()) {
            var = getSimpleVarFromTypespec(fC, declarationId, nameId, tps,
                                           ranges, compileDesign);
            if ((ts != nullptr) && (var != nullptr)) {
              if (var->getTypespec() == nullptr) {
                uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
                tsRef->setParent(var);
                var->setTypespec(tsRef);
                fC->populateCoreMembers(declarationId, declarationId, tsRef);
              }
              var->getTypespec()->setActual(ts);
            }
            break;
          }
          dtype = dtype->getDefinition();
        }
      }
      if (var == nullptr) {
        ClassDefinition* cl = design->getClassDefinition(packageName);
        if (cl == nullptr) {
          cl = design->getClassDefinition(
              StrCat(component->getName(), "::", packageName));
        }
        if (cl == nullptr) {
          if (const DesignComponent* p =
                  valuedcomponenti_cast<const DesignComponent*>(
                      component->getParentScope())) {
            cl = design->getClassDefinition(
                StrCat(p->getName(), "::", packageName));
          }
        }
        if (cl) {
          const DataType* dtype = cl->getDataType(design, typeName);
          while (dtype) {
            if (uhdm::Typespec* tps = dtype->getTypespec()) {
              var = getSimpleVarFromTypespec(fC, declarationId, nameId, tps,
                                             ranges, compileDesign);
              if ((ts != nullptr) && (var != nullptr)) {
                if (var->getTypespec() == nullptr) {
                  uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
                  tsRef->setParent(var);
                  var->setTypespec(tsRef);
                  fC->populateCoreMembers(declarationId, declarationId, tsRef);
                }
                var->getTypespec()->setActual(ts);
              }
              break;
            }
            dtype = dtype->getDefinition();
          }
        }
      }

      const std::string completeName = StrCat(packageName, "::", typeName);
      if (var == nullptr) var = s.make<uhdm::ClassVar>();
      var->setName(completeName);
      uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
      tsRef->setName(completeName);
      tsRef->setParent(var);
      tsRef->setActual(ts);
      fC->populateCoreMembers(declarationId, declarationId, tsRef);
      var->setTypespec(tsRef);
      result = var;
      break;
    }
    case VObjectType::paString_type: {
      uhdm::StringVar* var = s.make<uhdm::StringVar>();
      uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
      tsRef->setParent(var);
      tsRef->setActual(ts);
      var->setTypespec(tsRef);
      var->setName(fC->SymName(nameId));
      fC->populateCoreMembers(nameId, nameId, var);
      fC->populateCoreMembers(declarationId, declarationId, tsRef);
      result = var;
      break;
    }
    case VObjectType::paVariable_lvalue: {
      NodeId hier_ident = fC->Child(variable);
      NodeId nameid = fC->Child(hier_ident);
      uhdm::IntVar* var = s.make<uhdm::IntVar>();
      var->setName(fC->SymName(nameid));
      uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
      tsRef->setParent(var);
      tsRef->setActual(ts);
      var->setTypespec(tsRef);
      fC->populateCoreMembers(declarationId, declarationId, tsRef);
      result = var;
      break;
    }
    default: {
      // Implicit type
      if (declarationId) {
        uhdm::LogicVar* var = s.make<uhdm::LogicVar>();
        var->setParent(pstmt);

        if (ts == nullptr) {
          uhdm::LogicTypespec* lts = s.make<uhdm::LogicTypespec>();
          lts->setSigned(isSigned);
          lts->setParent(var);
          fC->populateCoreMembers(declarationId, declarationId, lts);
          if ((ranges != nullptr) && !ranges->empty()) {
            lts->setRanges(ranges);
            for (uhdm::Range* r : *ranges) r->setParent(lts, true);
            lts->setEndLine(ranges->back()->getEndLine());
            lts->setEndColumn(ranges->back()->getEndColumn());
          }
          ts = lts;
        }

        uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
        tsRef->setParent(var);
        tsRef->setActual(ts);
        fC->populateCoreMembers(declarationId, declarationId, tsRef);
        var->setTypespec(tsRef);

        result = var;
      }
      break;
    }
  }
  if (result != nullptr) {
    result->setParent(pstmt);
    fC->populateCoreMembers(nameId, nameId, result);
  }
  return result;
}

uhdm::Any* CompileHelper::compileVariable(
    DesignComponent* component, CompileDesign* compileDesign, Signal* sig,
    std::vector<uhdm::Range*>* packedDimensions, int32_t packedSize,
    std::vector<uhdm::Range*>* unpackedDimensions, int32_t unpackedSize,
    uhdm::Expr* assignExp, uhdm::Typespec* tps) {
  uhdm::Serializer& s = compileDesign->getSerializer();
  const DataType* dtype = sig->getDataType();
  VObjectType subnettype = sig->getType();
  NodeId signalId = sig->getNameId();
  const std::string_view signame = sig->getName();
  const FileContent* const fC = sig->getFileContent();
  Design* const design = compileDesign->getCompiler()->getDesign();
  uhdm::Any* pscope = component->getUhdmModel();
  if (pscope == nullptr) pscope = design->getUhdmDesign();
  NodeId rtBeginId = sig->getInterfaceTypeNameId()
                         ? sig->getInterfaceTypeNameId()
                         : sig->getTypespecId();
  if (NodeId interfaceId =
          fC->sl_get(rtBeginId, VObjectType::paInterface_identifier)) {
    rtBeginId = interfaceId;
  }
  const NodeId rtEndId =
      sig->getPackedDimension() ? sig->getPackedDimension() : rtBeginId;

  uhdm::Variables* obj = nullptr;
  bool found = false;
  while (dtype) {
    if (const TypeDef* tdef = datatype_cast<TypeDef>(dtype)) {
      if (tdef->getTypespec()) {
        tps = tdef->getTypespec();
        found = false;
        break;
      }
    } else if (const Enum* en = datatype_cast<Enum>(dtype)) {
      if (en->getTypespec()) {
        uhdm::EnumVar* stv = s.make<uhdm::EnumVar>();
        if (uhdm::Typespec* ts = en->getTypespec()) {
          uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
          tsRef->setParent(stv);
          tsRef->setActual(ts);
          fC->populateCoreMembers(rtBeginId, rtEndId, tsRef);
          stv->setTypespec(tsRef);
        }
        if (assignExp != nullptr) {
          stv->setExpr(assignExp);
          assignExp->setParent(stv);
        }
        obj = stv;
        found = true;
        break;
      }
    } else if (const Struct* st = datatype_cast<Struct>(dtype)) {
      if (st->getTypespec()) {
        uhdm::StructVar* stv = s.make<uhdm::StructVar>();
        if (uhdm::Typespec* ts = st->getTypespec()) {
          uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
          tsRef->setParent(stv);
          tsRef->setActual(ts);
          fC->populateCoreMembers(rtBeginId, rtEndId, tsRef);
          stv->setTypespec(tsRef);
        }
        if (assignExp != nullptr) {
          stv->setExpr(assignExp);
          assignExp->setParent(stv);
        }
        obj = stv;
        found = true;
        break;
      }
    } else if (const Union* un = datatype_cast<Union>(dtype)) {
      if (un->getTypespec()) {
        uhdm::UnionVar* stv = s.make<uhdm::UnionVar>();
        if (uhdm::Typespec* ts = un->getTypespec()) {
          uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
          tsRef->setParent(stv);
          tsRef->setActual(ts);
          fC->populateCoreMembers(rtBeginId, rtEndId, tsRef);
          stv->setTypespec(tsRef);
        }
        if (assignExp != nullptr) {
          stv->setExpr(assignExp);
          assignExp->setParent(stv);
        }
        obj = stv;
        found = true;
        break;
      }
    } else if (const DummyType* un = datatype_cast<DummyType>(dtype)) {
      uhdm::Typespec* tps = un->getTypespec();
      if (tps == nullptr) {
        tps =
            compileTypespec(component, un->getFileContent(), un->getNodeId(),
                            compileDesign, Reduce::Yes, nullptr, nullptr, true);
        ((DummyType*)un)->setTypespec(tps);
      }
      uhdm::Variables* var = nullptr;
      uhdm::UhdmType ttps = tps->getUhdmType();
      if (ttps == uhdm::UhdmType::EnumTypespec) {
        var = s.make<uhdm::EnumVar>();
      } else if (ttps == uhdm::UhdmType::StructTypespec) {
        var = s.make<uhdm::StructVar>();
      } else if (ttps == uhdm::UhdmType::UnionTypespec) {
        var = s.make<uhdm::UnionVar>();
      } else if (ttps == uhdm::UhdmType::PackedArrayTypespec) {
        var = s.make<uhdm::PackedArrayVar>();
      } else if (ttps == uhdm::UhdmType::ArrayTypespec) {
        uhdm::ArrayVar* array_var = s.make<uhdm::ArrayVar>();
        uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
        tsRef->setParent(array_var);
        tsRef->setActual(s.make<uhdm::ArrayTypespec>());
        fC->populateCoreMembers(rtBeginId, rtEndId, tsRef);
        array_var->setTypespec(tsRef);
        array_var->setArrayType(vpiStaticArray);
        array_var->setRandType(vpiNotRand);
        var = array_var;
      } else if (ttps == uhdm::UhdmType::IntTypespec) {
        var = s.make<uhdm::IntVar>();
      } else if (ttps == uhdm::UhdmType::IntegerTypespec) {
        var = s.make<uhdm::IntegerVar>();
      } else if (ttps == uhdm::UhdmType::ByteTypespec) {
        var = s.make<uhdm::ByteVar>();
      } else if (ttps == uhdm::UhdmType::BitTypespec) {
        var = s.make<uhdm::BitVar>();
      } else if (ttps == uhdm::UhdmType::ShortIntTypespec) {
        var = s.make<uhdm::ShortIntVar>();
      } else if (ttps == uhdm::UhdmType::LongIntTypespec) {
        var = s.make<uhdm::LongIntVar>();
      } else if (ttps == uhdm::UhdmType::StringTypespec) {
        var = s.make<uhdm::StringVar>();
      } else if (ttps == uhdm::UhdmType::LogicTypespec) {
        uhdm::LogicTypespec* ltps = (uhdm::LogicTypespec*)tps;
        uhdm::LogicVar* avar = s.make<uhdm::LogicVar>();
        if (auto ranges = ltps->getRanges()) {
          avar->setRanges(ranges);
          for (uhdm::Range* r : *ranges) r->setParent(avar, true);
        }
        var = avar;
      } else {
        var = s.make<uhdm::LogicVar>();
      }
      var->setName(signame);
      if (var->getTypespec() == nullptr) {
        uhdm::RefTypespec* tpsRef = s.make<uhdm::RefTypespec>();
        tpsRef->setParent(var);
        fC->populateCoreMembers(rtBeginId, rtEndId, tpsRef);
        var->setTypespec(tpsRef);
      }
      var->getTypespec()->setActual(tps);
      if (assignExp != nullptr) {
        var->setExpr(assignExp);
        assignExp->setParent(var);
      }
      obj = var;
      found = true;
      break;
    } else if (const SimpleType* sit = datatype_cast<SimpleType>(dtype)) {
      uhdm::Typespec* spec = sit->getTypespec();
      spec = elabTypespec(component, spec, compileDesign, nullptr, nullptr);
      if (uhdm::Variables* var =
              getSimpleVarFromTypespec(fC, sit->getNodeId(), sit->getNodeId(),
                                       spec, packedDimensions, compileDesign)) {
        var->setConstantVariable(sig->isConst());
        var->setSigned(sig->isSigned());
        var->setName(signame);
        if (var->getTypespec() == nullptr) {
          uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
          tsRef->setParent(var);
          fC->populateCoreMembers(rtBeginId, rtEndId, tsRef);
          var->setTypespec(tsRef);
        }
        var->getTypespec()->setActual(spec);
        if (assignExp != nullptr) {
          var->setExpr(assignExp);
          assignExp->setParent(var);
        }
        obj = var;
      }
      found = true;
      break;
    } else if (/*const ClassDefinition* cl = */ datatype_cast<ClassDefinition>(
        dtype)) {
      uhdm::ClassVar* stv = s.make<uhdm::ClassVar>();
      uhdm::RefTypespec* tpsRef = s.make<uhdm::RefTypespec>();
      tpsRef->setParent(stv);
      tpsRef->setActual(tps);
      fC->populateCoreMembers(rtBeginId, rtEndId, tpsRef);
      stv->setTypespec(tpsRef);
      if (assignExp != nullptr) {
        stv->setExpr(assignExp);
        assignExp->setParent(stv);
      }
      obj = stv;
      found = true;
      break;
    } else if (Parameter* sit =
                   const_cast<Parameter*>(datatype_cast<Parameter>(dtype))) {
      if (uhdm::Typespec* spec =
              compileTypeParameter(component, compileDesign, sit)) {
        if (uhdm::Variables* var = getSimpleVarFromTypespec(
                fC, sit->getNodeId(), sit->getNodeId(), spec, packedDimensions,
                compileDesign)) {
          var->setConstantVariable(sig->isConst());
          var->setSigned(sig->isSigned());
          var->setName(signame);
          if (assignExp != nullptr) {
            var->setExpr(assignExp);
            assignExp->setParent(var);
          }
          obj = var;
          found = true;
          break;
        }
      }
    }
    dtype = dtype->getDefinition();
  }

  if ((found == false) && tps) {
    uhdm::UhdmType tpstype = tps->getUhdmType();
    if (tpstype == uhdm::UhdmType::StructTypespec) {
      uhdm::StructVar* stv = s.make<uhdm::StructVar>();
      obj = stv;
    } else if (tpstype == uhdm::UhdmType::LogicTypespec) {
      uhdm::LogicVar* stv = s.make<uhdm::LogicVar>();
      // Do not set packedDimensions, it is a repeat of the typespec packed
      // dimension.
      // stv->setRanges(packedDimensions);
      obj = stv;
    } else if (tpstype == uhdm::UhdmType::EnumTypespec) {
      uhdm::EnumVar* stv = s.make<uhdm::EnumVar>();
      obj = stv;
    } else if (tpstype == uhdm::UhdmType::BitTypespec) {
      uhdm::BitVar* stv = s.make<uhdm::BitVar>();
      obj = stv;
    } else if (tpstype == uhdm::UhdmType::ByteTypespec) {
      uhdm::ByteVar* stv = s.make<uhdm::ByteVar>();
      obj = stv;
    } else if (tpstype == uhdm::UhdmType::RealTypespec) {
      uhdm::RealVar* stv = s.make<uhdm::RealVar>();
      obj = stv;
    } else if (tpstype == uhdm::UhdmType::IntTypespec) {
      uhdm::IntVar* stv = s.make<uhdm::IntVar>();
      obj = stv;
    } else if (tpstype == uhdm::UhdmType::IntegerTypespec) {
      uhdm::IntegerVar* stv = s.make<uhdm::IntegerVar>();
      obj = stv;
    } else if (tpstype == uhdm::UhdmType::LongIntTypespec) {
      uhdm::LongIntVar* stv = s.make<uhdm::LongIntVar>();
      obj = stv;
    } else if (tpstype == uhdm::UhdmType::ShortIntTypespec) {
      uhdm::ShortIntVar* stv = s.make<uhdm::ShortIntVar>();
      obj = stv;
    } else if (tpstype == uhdm::UhdmType::StringTypespec) {
      uhdm::StringVar* stv = s.make<uhdm::StringVar>();
      obj = stv;
    } else if (tpstype == uhdm::UhdmType::BitTypespec) {
      uhdm::BitVar* stv = s.make<uhdm::BitVar>();
      obj = stv;
    } else if (tpstype == uhdm::UhdmType::ByteTypespec) {
      uhdm::ByteVar* stv = s.make<uhdm::ByteVar>();
      obj = stv;
    } else if (tpstype == uhdm::UhdmType::TimeTypespec) {
      uhdm::TimeVar* stv = s.make<uhdm::TimeVar>();
      obj = stv;
    } else if (tpstype == uhdm::UhdmType::UnionTypespec) {
      uhdm::UnionVar* stv = s.make<uhdm::UnionVar>();
      obj = stv;
    } else if (tpstype == uhdm::UhdmType::ClassTypespec) {
      uhdm::ClassVar* stv = s.make<uhdm::ClassVar>();
      obj = stv;
    } else if (tpstype == uhdm::UhdmType::PackedArrayTypespec) {
      uhdm::PackedArrayVar* stv = s.make<uhdm::PackedArrayVar>();
      obj = stv;
    } else if (tpstype == uhdm::UhdmType::ArrayTypespec) {
      uhdm::ArrayVar* stv = s.make<uhdm::ArrayVar>();
      obj = stv;
    } else if (tpstype == uhdm::UhdmType::InterfaceTypespec) {
      uhdm::VirtualInterfaceVar* stv = s.make<uhdm::VirtualInterfaceVar>();
      obj = stv;
    }

    if (obj != nullptr) {
      obj->setName(signame);
      obj->setParent(pscope);
      fC->populateCoreMembers(signalId, signalId, obj);
      if (assignExp != nullptr) {
        assignExp->setParent(obj);
        obj->setExpr(assignExp);
      }
      if (tps != nullptr) {
        if (obj->getTypespec() == nullptr) {
          uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
          rt->setParent(obj);
          obj->setTypespec(rt);
          rt->setName(fC->SymName(rtBeginId));
          fC->populateCoreMembers(rtBeginId, rtEndId, rt);
          if ((tpstype == uhdm::UhdmType::ClassTypespec) &&
              (rt->getName().empty() ||
               (rt->getName() == SymbolTable::getBadSymbol())))
            rt->setName(tps->getName());
        }
        obj->getTypespec()->setActual(tps);
        tps->setParent(obj);
      }
    }
  }

  if (obj == nullptr) {
    uhdm::Variables* var = nullptr;
    if (subnettype == VObjectType::paIntegerAtomType_Shortint) {
      uhdm::ShortIntVar* int_var = s.make<uhdm::ShortIntVar>();
      fC->populateCoreMembers(signalId, signalId, int_var);
      var = int_var;
      tps = s.make<uhdm::ShortIntTypespec>();
      tps->setParent(pscope);
      uhdm::RefTypespec* tpsRef = s.make<uhdm::RefTypespec>();
      tpsRef->setParent(int_var);
      tpsRef->setActual(tps);
      int_var->setTypespec(tpsRef);
      fC->populateCoreMembers(rtBeginId, rtEndId, tpsRef);
      fC->populateCoreMembers(rtBeginId, rtEndId, tps);
    } else if (subnettype == VObjectType::paIntegerAtomType_Int) {
      uhdm::IntVar* int_var = s.make<uhdm::IntVar>();
      fC->populateCoreMembers(signalId, signalId, int_var);
      var = int_var;
      tps = s.make<uhdm::IntTypespec>();
      tps->setParent(pscope);
      uhdm::RefTypespec* tpsRef = s.make<uhdm::RefTypespec>();
      tpsRef->setParent(int_var);
      tpsRef->setActual(tps);
      int_var->setTypespec(tpsRef);
      fC->populateCoreMembers(rtBeginId, rtEndId, tpsRef);
      fC->populateCoreMembers(rtBeginId, rtEndId, tps);
    } else if (subnettype == VObjectType::paIntegerAtomType_Integer) {
      uhdm::IntegerVar* int_var = s.make<uhdm::IntegerVar>();
      fC->populateCoreMembers(signalId, signalId, int_var);
      var = int_var;
      tps = s.make<uhdm::IntegerTypespec>();
      tps->setParent(pscope);
      uhdm::RefTypespec* tpsRef = s.make<uhdm::RefTypespec>();
      tpsRef->setParent(int_var);
      tpsRef->setActual(tps);
      int_var->setTypespec(tpsRef);
      fC->populateCoreMembers(rtBeginId, rtEndId, tpsRef);
      fC->populateCoreMembers(rtBeginId, rtEndId, tps);
    } else if (subnettype == VObjectType::paIntegerAtomType_LongInt) {
      uhdm::LongIntVar* int_var = s.make<uhdm::LongIntVar>();
      fC->populateCoreMembers(signalId, signalId, int_var);
      var = int_var;
      tps = s.make<uhdm::LongIntTypespec>();
      tps->setParent(pscope);
      uhdm::RefTypespec* tpsRef = s.make<uhdm::RefTypespec>();
      tpsRef->setParent(int_var);
      tpsRef->setActual(tps);
      int_var->setTypespec(tpsRef);
      fC->populateCoreMembers(rtBeginId, rtEndId, tpsRef);
      fC->populateCoreMembers(rtBeginId, rtEndId, tps);
    } else if (subnettype == VObjectType::paIntegerAtomType_Time) {
      uhdm::TimeVar* int_var = s.make<uhdm::TimeVar>();
      fC->populateCoreMembers(signalId, signalId, int_var);
      var = int_var;
    } else if (subnettype == VObjectType::paIntVec_TypeBit) {
      uhdm::BitVar* int_var = s.make<uhdm::BitVar>();
      fC->populateCoreMembers(signalId, signalId, int_var);
      uhdm::BitTypespec* btps = s.make<uhdm::BitTypespec>();
      if (packedDimensions != nullptr) {
        btps->setRanges(packedDimensions);
        for (uhdm::Range* r : *packedDimensions) r->setParent(btps, true);
      }
      btps->setParent(pscope);
      tps = btps;
      uhdm::RefTypespec* tpsRef = s.make<uhdm::RefTypespec>();
      tpsRef->setParent(int_var);
      tpsRef->setActual(tps);
      int_var->setTypespec(tpsRef);
      fC->populateCoreMembers(rtBeginId, rtEndId, tpsRef);
      fC->populateCoreMembers(rtBeginId, rtEndId, tps);
      var = int_var;
    } else if (subnettype == VObjectType::paIntegerAtomType_Byte) {
      uhdm::ByteVar* int_var = s.make<uhdm::ByteVar>();
      fC->populateCoreMembers(signalId, signalId, int_var);
      uhdm::ByteTypespec* btps = s.make<uhdm::ByteTypespec>();
      btps->setParent(pscope);
      tps = btps;
      uhdm::RefTypespec* tpsRef = s.make<uhdm::RefTypespec>();
      tpsRef->setParent(int_var);
      tpsRef->setActual(tps);
      int_var->setTypespec(tpsRef);
      fC->populateCoreMembers(rtBeginId, rtEndId, tpsRef);
      fC->populateCoreMembers(rtBeginId, rtEndId, tps);
      var = int_var;
    } else if (subnettype == VObjectType::paNonIntType_ShortReal) {
      uhdm::ShortRealVar* int_var = s.make<uhdm::ShortRealVar>();
      fC->populateCoreMembers(signalId, signalId, int_var);
      var = int_var;
    } else if (subnettype == VObjectType::paNonIntType_Real) {
      uhdm::RealVar* int_var = s.make<uhdm::RealVar>();
      fC->populateCoreMembers(signalId, signalId, int_var);
      var = int_var;
    } else if (subnettype == VObjectType::paNonIntType_RealTime) {
      uhdm::TimeVar* int_var = s.make<uhdm::TimeVar>();
      fC->populateCoreMembers(signalId, signalId, int_var);
      var = int_var;
    } else if (subnettype == VObjectType::paString_type) {
      uhdm::StringVar* int_var = s.make<uhdm::StringVar>();
      fC->populateCoreMembers(signalId, signalId, int_var);
      var = int_var;
    } else if (subnettype == VObjectType::paChandle_type) {
      uhdm::ChandleVar* chandle_var = s.make<uhdm::ChandleVar>();
      fC->populateCoreMembers(signalId, signalId, chandle_var);
      var = chandle_var;
    } else if (subnettype == VObjectType::paIntVec_TypeLogic) {
      uhdm::LogicVar* logicv = s.make<uhdm::LogicVar>();
      uhdm::LogicTypespec* ltps = s.make<uhdm::LogicTypespec>();
      ltps->setParent(pscope);
      NodeId id;
      if (sig->getPackedDimension()) id = fC->Parent(sig->getPackedDimension());
      if (!id) id = sig->getNodeId();
      if (id) fC->populateCoreMembers(id, id, ltps);
      if ((packedDimensions != nullptr) && !packedDimensions->empty()) {
        ltps->setRanges(packedDimensions);
        for (uhdm::Range* r : *packedDimensions) r->setParent(ltps, true);
        ltps->setEndLine(packedDimensions->back()->getEndLine());
        ltps->setEndColumn(packedDimensions->back()->getEndColumn());
      }
      tps = ltps;
      uhdm::RefTypespec* tpsRef = s.make<uhdm::RefTypespec>();
      tpsRef->setParent(logicv);
      tpsRef->setActual(tps);
      fC->populateCoreMembers(rtBeginId, rtEndId, tpsRef);
      logicv->setTypespec(tpsRef);
      var = logicv;
    } else if (subnettype == VObjectType::paEvent_type) {
      uhdm::NamedEvent* event = s.make<uhdm::NamedEvent>();
      event->setName(signame);
      return event;
    } else {
      // default type (fallback)
      uhdm::LogicVar* logicv = s.make<uhdm::LogicVar>();
      if (packedDimensions != nullptr) {
        logicv->setRanges(packedDimensions);
        for (uhdm::Range* r : *packedDimensions) r->setParent(logicv, true);
      }
      var = logicv;
    }
    var->setSigned(sig->isSigned());
    var->setConstantVariable(sig->isConst());
    var->setName(signame);
    if (assignExp != nullptr) {
      var->setExpr(assignExp);
      assignExp->setParent(var);
    }
    obj = var;
  } else if (packedDimensions &&
             (obj->getUhdmType() != uhdm::UhdmType::LogicVar) &&
             (obj->getUhdmType() != uhdm::UhdmType::BitVar) &&
             (obj->getUhdmType() != uhdm::UhdmType::PackedArrayVar)) {
    // packed struct array ...
    uhdm::PackedArrayVar* parray = s.make<uhdm::PackedArrayVar>();
    if (packedDimensions != nullptr) {
      parray->setRanges(packedDimensions);
      for (uhdm::Range* r : *packedDimensions) r->setParent(parray, true);
    }
    parray->getElements(true)->emplace_back(obj);
    obj->setParent(parray);
    parray->setName(signame);
    obj = parray;
  }

  if (unpackedDimensions) {
    uhdm::ArrayVar* array_var = s.make<uhdm::ArrayVar>();
    array_var->setParent(pscope);
    bool dynamic = false;
    bool associative = false;
    bool queue = false;
    int32_t index = 0;
    for (auto itr = unpackedDimensions->begin();
         itr != unpackedDimensions->end(); itr++) {
      uhdm::Range* r = *itr;
      const uhdm::Expr* rhs = r->getRightExpr();
      if (rhs->getUhdmType() == uhdm::UhdmType::Constant) {
        const std::string_view value = rhs->getValue();
        if (value == "STRING:$") {
          queue = true;
          unpackedDimensions->erase(itr);
          break;
        } else if (value == "STRING:associative") {
          associative = true;
          const uhdm::Typespec* tp = nullptr;
          if (const uhdm::RefTypespec* rt = rhs->getTypespec()) {
            tp = rt->getActual();
          }

          uhdm::ArrayTypespec* taps = s.make<uhdm::ArrayTypespec>();
          taps->setParent(pscope);
          fC->populateCoreMembers(signalId, signalId, taps);

          if (tps != nullptr) {
            uhdm::RefTypespec* ert = s.make<uhdm::RefTypespec>();
            ert->setParent(taps);
            ert->setActual(tps);
            ert->setName(tps->getName());
            taps->setElemTypespec(ert);
            fC->populateCoreMembers(sig->getTypespecId(), sig->getTypespecId(),
                                    ert);
          }

          if (tp != nullptr) {
            uhdm::RefTypespec* tpRef = s.make<uhdm::RefTypespec>();
            tpRef->setParent(taps);
            tpRef->setName(tp->getName());
            tpRef->setActual(const_cast<uhdm::Typespec*>(tp));
            taps->setIndexTypespec(tpRef);
            fC->populateCoreMembers(sig->getUnpackedDimension(),
                                    sig->getUnpackedDimension(), tpRef);
          }

          uhdm::RefTypespec* taps_ref = s.make<uhdm::RefTypespec>();
          taps_ref->setParent(array_var);
          taps_ref->setActual(taps);
          taps_ref->setName(array_var->getName());
          fC->populateCoreMembers(sig->getUnpackedDimension(),
                                  sig->getUnpackedDimension(), taps_ref);
          array_var->setTypespec(taps_ref);
          unpackedDimensions->erase(itr);
          break;
        } else if (value == "STRING:unsized") {
          dynamic = true;
          unpackedDimensions->erase(itr);
          break;
        }
      }
      index++;
    }

    if (associative || queue || dynamic) {
      if (!unpackedDimensions->empty()) {
        if (index == 0) {
          array_var->setRanges(unpackedDimensions);
          for (uhdm::Range* r : *unpackedDimensions)
            r->setParent(array_var, true);
        } else {
          uhdm::ArrayTypespec* tps = s.make<uhdm::ArrayTypespec>();
          uhdm::RefTypespec* tpsRef = s.make<uhdm::RefTypespec>();
          tpsRef->setParent(array_var);
          tps->setParent(pscope);
          tpsRef->setActual(tps);
          NodeId unpackDimensionId = sig->getUnpackedDimension();
          while (fC->Sibling(unpackDimensionId))
            unpackDimensionId = fC->Sibling(unpackDimensionId);
          fC->populateCoreMembers(unpackDimensionId, unpackDimensionId, tpsRef);
          fC->populateCoreMembers(unpackDimensionId, unpackDimensionId, tps);
          array_var->setTypespec(tpsRef);

          if (associative)
            tps->setArrayType(vpiAssocArray);
          else if (queue)
            tps->setArrayType(vpiQueueArray);
          else if (dynamic)
            tps->setArrayType(vpiDynamicArray);
          else
            tps->setArrayType(vpiStaticArray);

          uhdm::ArrayTypespec* subtps = s.make<uhdm::ArrayTypespec>();
          subtps->setParent(pscope);
          fC->populateCoreMembers(sig->getUnpackedDimension(),
                                  sig->getUnpackedDimension(), subtps);
          array_var->setTypespec(tpsRef);
          tpsRef = s.make<uhdm::RefTypespec>();
          fC->populateCoreMembers(signalId, signalId, tpsRef);
          tpsRef->setParent(tps);
          tpsRef->setActual(subtps);
          tps->setElemTypespec(tpsRef);

          subtps->setRanges(unpackedDimensions);
          for (uhdm::Range* r : *unpackedDimensions) r->setParent(subtps, true);
          subtps->setEndLine(unpackedDimensions->back()->getEndLine());
          subtps->setEndColumn(unpackedDimensions->back()->getEndColumn());

          switch (obj->getUhdmType()) {
            case uhdm::UhdmType::IntVar: {
              uhdm::IntTypespec* ts = s.make<uhdm::IntTypespec>();
              fC->populateCoreMembers(rtBeginId, rtEndId, ts);
              ts->setParent(pscope);
              tpsRef = s.make<uhdm::RefTypespec>();
              tpsRef->setParent(subtps);
              tpsRef->setActual(ts);
              subtps->setElemTypespec(tpsRef);
              break;
            }
            case uhdm::UhdmType::IntegerVar: {
              uhdm::IntegerTypespec* ts = s.make<uhdm::IntegerTypespec>();
              fC->populateCoreMembers(rtBeginId, rtEndId, ts);
              ts->setParent(pscope);
              tpsRef = s.make<uhdm::RefTypespec>();
              tpsRef->setParent(subtps);
              tpsRef->setActual(ts);
              subtps->setElemTypespec(tpsRef);
              break;
            }
            case uhdm::UhdmType::LogicVar: {
              uhdm::LogicTypespec* ts = s.make<uhdm::LogicTypespec>();
              fC->populateCoreMembers(rtBeginId, rtEndId, ts);
              ts->setParent(pscope);
              tpsRef = s.make<uhdm::RefTypespec>();
              tpsRef->setParent(subtps);
              tpsRef->setActual(ts);
              subtps->setElemTypespec(tpsRef);
              break;
            }
            case uhdm::UhdmType::LongIntVar: {
              uhdm::LongIntTypespec* ts = s.make<uhdm::LongIntTypespec>();
              fC->populateCoreMembers(rtBeginId, rtEndId, ts);
              ts->setParent(pscope);
              tpsRef = s.make<uhdm::RefTypespec>();
              tpsRef->setParent(subtps);
              tpsRef->setActual(ts);
              subtps->setElemTypespec(tpsRef);
              break;
            }
            case uhdm::UhdmType::ShortIntVar: {
              uhdm::ShortIntTypespec* ts = s.make<uhdm::ShortIntTypespec>();
              fC->populateCoreMembers(rtBeginId, rtEndId, ts);
              ts->setParent(pscope);
              tpsRef = s.make<uhdm::RefTypespec>();
              tpsRef->setParent(subtps);
              tpsRef->setActual(ts);
              subtps->setElemTypespec(tpsRef);
              break;
            }
            case uhdm::UhdmType::ByteVar: {
              uhdm::ByteTypespec* ts = s.make<uhdm::ByteTypespec>();
              fC->populateCoreMembers(rtBeginId, rtEndId, ts);
              ts->setParent(pscope);
              tpsRef = s.make<uhdm::RefTypespec>();
              tpsRef->setParent(subtps);
              tpsRef->setActual(ts);
              subtps->setElemTypespec(tpsRef);
              break;
            }
            case uhdm::UhdmType::BitVar: {
              uhdm::BitTypespec* ts = s.make<uhdm::BitTypespec>();
              fC->populateCoreMembers(rtBeginId, rtEndId, ts);
              ts->setParent(pscope);
              tpsRef = s.make<uhdm::RefTypespec>();
              tpsRef->setParent(subtps);
              tpsRef->setActual(ts);
              subtps->setElemTypespec(tpsRef);
              break;
            }
            case uhdm::UhdmType::StringVar: {
              uhdm::StringTypespec* ts = s.make<uhdm::StringTypespec>();
              fC->populateCoreMembers(rtBeginId, rtEndId, ts);
              ts->setParent(pscope);
              tpsRef = s.make<uhdm::RefTypespec>();
              tpsRef->setParent(subtps);
              tpsRef->setActual(ts);
              subtps->setElemTypespec(tpsRef);
              break;
            }
            default: {
              uhdm::UnsupportedTypespec* ts =
                  s.make<uhdm::UnsupportedTypespec>();
              tpsRef = s.make<uhdm::RefTypespec>();
              ts->setName(fC->SymName(rtBeginId));
              ts->setParent(pscope);
              fC->populateCoreMembers(rtBeginId, rtEndId, ts);
              tpsRef->setName(fC->SymName(rtBeginId));
              tpsRef->setParent(subtps);
              tpsRef->setActual(ts);
              subtps->setElemTypespec(tpsRef);
              break;
            }
          }
          fC->populateCoreMembers(rtBeginId, rtEndId, tpsRef);
        }
      }
    }

    if (associative) {
      array_var->setArrayType(vpiAssocArray);
    } else if (queue) {
      array_var->setArrayType(vpiQueueArray);
    } else if (dynamic) {
      array_var->setArrayType(vpiDynamicArray);
    } else {
      if (unpackedDimensions != nullptr) {
        array_var->setRanges(unpackedDimensions);
        for (uhdm::Range* r : *unpackedDimensions)
          r->setParent(array_var, true);
      }
      array_var->setArrayType(vpiStaticArray);
    }
    array_var->setSize(unpackedSize);
    array_var->setName(signame);
    array_var->setRandType(vpiNotRand);
    array_var->setVisibility(vpiPublicVis);
    fC->populateCoreMembers(sig->getNameId(), sig->getNameId(), array_var);

    obj->setParent(pscope);
    if ((array_var->getTypespec() == nullptr) || associative) {
      array_var->getVariables(true)->emplace_back(obj);
      obj->setName("");
    }
    if (array_var->getTypespec() == nullptr) {
      uhdm::ArrayTypespec* attps = s.make<uhdm::ArrayTypespec>();
      fC->populateCoreMembers(sig->getUnpackedDimension(),
                              sig->getUnpackedDimension(), attps);
      attps->setParent(pscope);

      if (tps != nullptr) {
        uhdm::RefTypespec* ert = s.make<uhdm::RefTypespec>();
        ert->setParent(attps);
        ert->setActual(tps);
        ert->setName(tps->getName());
        attps->setElemTypespec(ert);
        if (sig->getInterfaceTypeNameId()) {
          fC->populateCoreMembers(sig->getInterfaceTypeNameId(),
                                  sig->getInterfaceTypeNameId(), ert);
        } else {
          fC->populateCoreMembers(sig->getTypespecId(), sig->getTypespecId(),
                                  ert);
        }
      }

      uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
      tsRef->setParent(array_var);
      tsRef->setActual(attps);
      array_var->setTypespec(tsRef);
      fC->populateCoreMembers(sig->getUnpackedDimension(),
                              sig->getUnpackedDimension(), tsRef);
    }
    if (assignExp != nullptr) {
      array_var->setExpr(assignExp);
      assignExp->setParent(array_var);
    }
    fC->populateCoreMembers(sig->getNameId(), sig->getNameId(), obj);
    obj = array_var;
  } else {
    if (obj->getUhdmType() == uhdm::UhdmType::EnumVar) {
      ((uhdm::EnumVar*)obj)->setName(signame);
    } else if (obj->getUhdmType() == uhdm::UhdmType::StructVar) {
      ((uhdm::StructVar*)obj)->setName(signame);
    } else if (obj->getUhdmType() == uhdm::UhdmType::UnionVar) {
      ((uhdm::UnionVar*)obj)->setName(signame);
    } else if (obj->getUhdmType() == uhdm::UhdmType::ClassVar) {
      ((uhdm::ClassVar*)obj)->setName(signame);
    } else if (obj->getUhdmType() == uhdm::UhdmType::LogicVar) {
      ((uhdm::LogicVar*)obj)->setName(signame);
    }
  }

  if (assignExp) {
    if (assignExp->getUhdmType() == uhdm::UhdmType::Constant) {
      adjustSize(tps, component, compileDesign, nullptr,
                 (uhdm::Constant*)assignExp);
    } else if (assignExp->getUhdmType() == uhdm::UhdmType::Operation) {
      uhdm::Operation* op = (uhdm::Operation*)assignExp;
      int32_t opType = op->getOpType();
      const uhdm::Typespec* tp = tps;
      if (opType == vpiAssignmentPatternOp) {
        if (tp->getUhdmType() == uhdm::UhdmType::PackedArrayTypespec) {
          uhdm::PackedArrayTypespec* ptp = (uhdm::PackedArrayTypespec*)tp;
          if (const uhdm::RefTypespec* ert = ptp->getElemTypespec()) {
            tp = ert->getActual();
          }
          if (tp == nullptr) tp = tps;
        }
      }
      for (auto oper : *op->getOperands()) {
        if (oper->getUhdmType() == uhdm::UhdmType::Constant)
          adjustSize(tp, component, compileDesign, nullptr,
                     (uhdm::Constant*)oper, false, true);
      }
    }
  }

  if (obj) {
    if (packedDimensions != nullptr) {
      for (auto r : *packedDimensions) r->setParent(obj);
    }
    if (unpackedDimensions != nullptr) {
      for (auto r : *unpackedDimensions) r->setParent(obj);
    }

    if (assignExp != nullptr) {
      obj->setExpr(assignExp);
      assignExp->setParent(obj);
    }
    obj->setSigned(sig->isSigned());
    obj->setConstantVariable(sig->isConst());
    obj->setIsRandomized(sig->isRand() || sig->isRandc());
    if (sig->isRand())
      obj->setRandType(vpiRand);
    else if (sig->isRandc())
      obj->setRandType(vpiRandC);
    if (sig->isStatic()) {
      obj->setAutomatic(false);
    } else {
      obj->setAutomatic(true);
    }
    if (sig->isProtected()) {
      obj->setVisibility(vpiProtectedVis);
    } else if (sig->isLocal()) {
      obj->setVisibility(vpiLocalVis);
    } else {
      obj->setVisibility(vpiPublicVis);
    }
  }
  obj->setParent(pscope);
  return obj;
}

uhdm::Typespec* CompileHelper::compileTypeParameter(
    DesignComponent* component, CompileDesign* compileDesign, Parameter* sit) {
  uhdm::Serializer& s = compileDesign->getSerializer();
  uhdm::Typespec* spec = nullptr;
  bool type_param = false;
  if (uhdm::Any* uparam = sit->getUhdmParam()) {
    if (uparam->getUhdmType() == uhdm::UhdmType::TypeParameter) {
      if (uhdm::RefTypespec* rt = ((uhdm::TypeParameter*)uparam)->getTypespec())
        spec = rt->getActual();
      type_param = true;
    } else {
      if (uhdm::RefTypespec* rt = ((uhdm::Parameter*)uparam)->getTypespec())
        spec = rt->getActual();
    }
  }

  const std::string_view pname = sit->getName();
  Parameter* param = component->getParameter(pname);

  uhdm::Any* uparam = param->getUhdmParam();
  uhdm::Typespec* override_spec = nullptr;
  if (uparam == nullptr) {
    if (type_param) {
      uhdm::TypeParameter* tp = s.make<uhdm::TypeParameter>();
      tp->setName(pname);
      param->setUhdmParam(tp);
    } else {
      uhdm::Parameter* tp = s.make<uhdm::Parameter>();
      tp->setName(pname);
      param->setUhdmParam(tp);
    }
    uparam = param->getUhdmParam();
  }

  if (type_param) {
    if (uhdm::RefTypespec* rt = ((uhdm::TypeParameter*)uparam)->getTypespec()) {
      override_spec = rt->getActual();
    }
  } else {
    if (uhdm::RefTypespec* rt = ((uhdm::Parameter*)uparam)->getTypespec()) {
      override_spec = rt->getActual();
    }
  }

  if (override_spec == nullptr) {
    override_spec = compileTypespec(component, param->getFileContent(),
                                    param->getNodeType(), compileDesign,
                                    Reduce::Yes, nullptr, nullptr, false);
  }

  if (override_spec) {
    if (type_param) {
      uhdm::TypeParameter* tparam = (uhdm::TypeParameter*)uparam;
      if (tparam->getTypespec() == nullptr) {
        uhdm::RefTypespec* override_specRef = s.make<uhdm::RefTypespec>();
        override_specRef->setParent(tparam);
        tparam->setTypespec(override_specRef);
      }
      tparam->getTypespec()->setActual(override_spec);
    } else {
      uhdm::Parameter* tparam = (uhdm::Parameter*)uparam;
      if (tparam->getTypespec() == nullptr) {
        uhdm::RefTypespec* override_specRef = s.make<uhdm::RefTypespec>();
        override_specRef->setParent(tparam);
        tparam->setTypespec(override_specRef);
      }
      tparam->getTypespec()->setActual(override_spec);
    }
    spec = override_spec;
    spec->setParent(uparam);
  }
  return spec;
}

const uhdm::Typespec* bindTypespec(Design* design, std::string_view name,
                                   SURELOG::ValuedComponentI* instance,
                                   uhdm::Serializer& s) {
  const uhdm::Typespec* result = nullptr;
  ModuleInstance* modInst = valuedcomponenti_cast<ModuleInstance*>(instance);
  while (modInst) {
    for (Parameter* param : modInst->getTypeParams()) {
      const std::string_view pname = param->getName();
      if (pname == name) {
        if (uhdm::Any* uparam = param->getUhdmParam()) {
          if (uhdm::TypeParameter* tparam =
                  any_cast<uhdm::TypeParameter>(uparam)) {
            if (const uhdm::RefTypespec* rt = tparam->getTypespec()) {
              result = rt->getActual();
            }
            uhdm::ElaboratorContext elaboratorContext(&s, false, true);
            result = any_cast<uhdm::Typespec>(
                uhdm::clone_tree((uhdm::Any*)result, &elaboratorContext));
          }
        }
        break;
      }
    }
    if (result == nullptr) {
      if (ModuleDefinition* mod = (ModuleDefinition*)modInst->getDefinition()) {
        if (Parameter* param = mod->getParameter(name)) {
          if (uhdm::Any* uparam = param->getUhdmParam()) {
            if (uhdm::TypeParameter* tparam =
                    any_cast<uhdm::TypeParameter>(uparam)) {
              if (const uhdm::RefTypespec* rt = tparam->getTypespec()) {
                result = rt->getActual();
              }
              uhdm::ElaboratorContext elaboratorContext(&s, false, true);
              result = any_cast<uhdm::Typespec>(
                  uhdm::clone_tree((uhdm::Any*)result, &elaboratorContext));
            }
          }
        }
        if (const DataType* dt = mod->getDataType(design, name)) {
          dt = dt->getActual();
          result = dt->getTypespec();
          uhdm::ElaboratorContext elaboratorContext(&s, false, true);
          result = any_cast<uhdm::Typespec>(
              uhdm::clone_tree((uhdm::Any*)result, &elaboratorContext));
        }
      }
    }
    modInst = modInst->getParent();
  }
  return result;
}

Typespec* CompileHelper::compileDatastructureTypespec(
    DesignComponent* component, const FileContent* fC, NodeId type,
    CompileDesign* compileDesign, Reduce reduce,
    SURELOG::ValuedComponentI* instance, std::string_view suffixname,
    std::string_view typeName) {
  SymbolTable* const symbols = m_session->getSymbolTable();
  ErrorContainer* const errors = m_session->getErrorContainer();
  CommandLineParser* const clp = m_session->getCommandLineParser();
  Design* const design = compileDesign->getCompiler()->getDesign();
  uhdm::Any* pscope = component->getUhdmModel();
  if (pscope == nullptr) pscope = design->getUhdmDesign();
  uhdm::Serializer& s = compileDesign->getSerializer();
  uhdm::Typespec* result = nullptr;
  if (component) {
    const DataType* dt = component->getDataType(design, typeName);
    if (dt == nullptr) {
      const std::string_view libName = fC->getLibrary()->getName();
      dt = design->getClassDefinition(StrCat(libName, "@", typeName));
      if (dt == nullptr) {
        dt = design->getClassDefinition(
            StrCat(component->getName(), "::", typeName));
      }
      if (dt == nullptr) {
        if (component->getParentScope())
          dt = design->getClassDefinition(
              StrCat(((DesignComponent*)component->getParentScope())->getName(),
                     "::", typeName));
      }
      if (dt == nullptr) {
        dt = design->getClassDefinition(typeName);
      }
      if (dt == nullptr) {
        Parameter* p = component->getParameter(typeName);
        if (p && p->getUhdmParam() &&
            (p->getUhdmParam()->getUhdmType() == uhdm::UhdmType::TypeParameter))
          dt = p;
      }
      if (dt == nullptr) {
        for (ParamAssign* passign : component->getParamAssignVec()) {
          const FileContent* fCP = passign->getFileContent();
          if (fCP->SymName(passign->getParamId()) == typeName) {
            uhdm::ParamAssign* param_assign = passign->getUhdmParamAssign();
            uhdm::Parameter* lhs = (uhdm::Parameter*)param_assign->getLhs();
            if (uhdm::RefTypespec* rt = lhs->getTypespec()) {
              result = rt->getActual();
            }
            if (result == nullptr) {
              if (uhdm::IntTypespec* tps = buildIntTypespec(
                      compileDesign, fC->getFileId(), typeName, "",
                      fC->Line(type), fC->Column(type), fC->EndLine(type),
                      fC->EndColumn(type))) {
                result = tps;
              }
            }
            if (result->getUhdmType() == uhdm::UhdmType::IntTypespec) {
              uhdm::IntTypespec* ts = (uhdm::IntTypespec*)result;
              uhdm::RefObj* ref = s.make<uhdm::RefObj>();
              ref->setActual(lhs);
              ref->setName(typeName);
              ref->setParent(ts);
              ts->setExpr(ref);
              fC->populateCoreMembers(type, type, ref);
            }
            return result;
          }
        }
      }
      if (dt == nullptr) {
        for (Signal* sig : component->getPorts()) {
          // Interface port type
          if ((sig->getName() == typeName) && sig->getInterfaceTypeNameId()) {
            std::string suffixname;
            std::string_view typeName2 = typeName;
            if (fC->Type(sig->getInterfaceTypeNameId()) ==
                VObjectType::slStringConst) {
              typeName2 = fC->SymName(sig->getInterfaceTypeNameId());
            }
            NodeId suffixNode;
            if ((suffixNode = fC->Sibling(type))) {
              if (fC->Type(suffixNode) == VObjectType::slStringConst) {
                suffixname = fC->SymName(suffixNode);
              } else if (fC->Type(suffixNode) ==
                         VObjectType::paConstant_bit_select) {
                suffixNode = fC->Sibling(suffixNode);
                if (fC->Type(suffixNode) == VObjectType::slStringConst) {
                  suffixname = fC->SymName(suffixNode);
                }
              }
            }
            uhdm::Typespec* tmp = compileDatastructureTypespec(
                component, fC, sig->getInterfaceTypeNameId(), compileDesign,
                reduce, instance, suffixname, typeName2);
            if (tmp) {
              if (tmp->getUhdmType() == uhdm::UhdmType::InterfaceTypespec) {
                if (!suffixname.empty()) {
                  Location loc1(fC->getFileId(), fC->Line(suffixNode),
                                fC->Column(suffixNode),
                                symbols->registerSymbol(suffixname));
                  const std::string_view libName = fC->getLibrary()->getName();
                  ModuleDefinition* def = design->getModuleDefinition(
                      StrCat(libName, "@", typeName2));
                  const FileContent* interF = def->getFileContents()[0];
                  Location loc2(interF->getFileId(),
                                interF->Line(def->getNodeIds()[0]),
                                interF->Column(def->getNodeIds()[0]),
                                symbols->registerSymbol(typeName2));
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
    if (dt == nullptr) {
      if (!clp->fileUnit()) {
        for (const auto& fC : design->getAllFileContents()) {
          if (const DataType* dt1 = fC.second->getDataType(design, typeName)) {
            dt = dt1;
            break;
          }
        }
      }
    }

    TypeDef* parent_tpd = nullptr;
    while (dt) {
      if (const TypeDef* tpd = datatype_cast<TypeDef>(dt)) {
        parent_tpd = (TypeDef*)tpd;
        if (parent_tpd->getTypespec()) {
          result = parent_tpd->getTypespec();
          break;
        }
      } else if (const Struct* st = datatype_cast<Struct>(dt)) {
        result = st->getTypespec();
        if (!suffixname.empty()) {
          uhdm::StructTypespec* tpss = (uhdm::StructTypespec*)result;
          for (uhdm::TypespecMember* memb : *tpss->getMembers()) {
            if (memb->getName() == suffixname) {
              if (uhdm::RefTypespec* rt = memb->getTypespec()) {
                result = rt->getActual();
              }
              break;
            }
          }
        }
        break;
      } else if (const Enum* en = datatype_cast<Enum>(dt)) {
        result = en->getTypespec();
        break;
      } else if (const Union* un = datatype_cast<Union>(dt)) {
        result = un->getTypespec();
        break;
      } else if (const DummyType* un = datatype_cast<DummyType>(dt)) {
        result = un->getTypespec();
      } else if (const SimpleType* sit = datatype_cast<SimpleType>(dt)) {
        result = sit->getTypespec();
        if ((m_elaborate == Elaborate::Yes) && parent_tpd && result) {
          uhdm::ElaboratorContext elaboratorContext(&s, false, true);
          if (uhdm::Typespec* new_result = any_cast<uhdm::Typespec>(
                  uhdm::clone_tree((uhdm::Any*)result, &elaboratorContext))) {
            if (uhdm::TypedefTypespec* const tt =
                    any_cast<uhdm::TypedefTypespec>(new_result)) {
              if (tt->getTypedefAlias() == nullptr) {
                uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
                fC->populateCoreMembers(type, type, tsRef);
                tsRef->setParent(new_result);
                tt->setTypedefAlias(tsRef);
              }
              tt->getTypedefAlias()->setActual(result);
            }
            result = new_result;
          }
        }
        break;
      } else if (/*const uhdm::Parameter* par = */ datatype_cast<Parameter>(
          dt)) {
        // Prevent circular definition
        return nullptr;
      } else if (const ClassDefinition* classDefn =
                     datatype_cast<ClassDefinition>(dt)) {
        uhdm::ClassTypespec* ref = s.make<uhdm::ClassTypespec>();
        ref->setClassDefn(classDefn->getUhdmModel<uhdm::ClassDefn>());
        ref->setName(typeName);
        ref->setParent(pscope);
        fC->populateCoreMembers(type, type, ref);
        result = ref;

        const FileContent* actualFC = fC;
        NodeId param = fC->Sibling(type);
        if (parent_tpd) {
          actualFC = parent_tpd->getFileContent();
          NodeId n = parent_tpd->getDefinitionNode();
          param = actualFC->Sibling(n);
        }
        if (param && (actualFC->Type(param) !=
                      VObjectType::paList_of_net_decl_assignments)) {
          uhdm::AnyCollection* params = ref->getParameters(true);
          uhdm::ParamAssignCollection* assigns = ref->getParamAssigns(true);
          uint32_t index = 0;
          NodeId Parameter_value_assignment = param;
          NodeId List_of_parameter_assignments =
              actualFC->Child(Parameter_value_assignment);
          NodeId Ordered_parameter_assignment =
              actualFC->Child(List_of_parameter_assignments);
          if (Ordered_parameter_assignment &&
              (actualFC->Type(Ordered_parameter_assignment) ==
               VObjectType::paOrdered_parameter_assignment)) {
            while (Ordered_parameter_assignment) {
              NodeId Param_expression =
                  actualFC->Child(Ordered_parameter_assignment);
              NodeId Data_type = actualFC->Child(Param_expression);
              std::string fName;
              const DesignComponent::ParameterVec& formal =
                  classDefn->getOrderedParameters();
              uhdm::Any* fparam = nullptr;
              if (index < formal.size()) {
                Parameter* p = formal.at(index);
                fName = p->getName();
                fparam = p->getUhdmParam();

                if (actualFC->Type(Data_type) == VObjectType::paData_type) {
                  uhdm::Typespec* tps = compileTypespec(
                      component, actualFC, Data_type, compileDesign, reduce,
                      result, instance, false);

                  uhdm::TypeParameter* tp = s.make<uhdm::TypeParameter>();
                  tp->setName(fName);
                  tp->setParent(ref);
                  tps->setParent(tp);
                  uhdm::RefTypespec* tpsRef = s.make<uhdm::RefTypespec>();
                  tpsRef->setParent(tp);
                  tpsRef->setName(fName);
                  tpsRef->setActual(tps);
                  tp->setTypespec(tpsRef);
                  p->getFileContent()->populateCoreMembers(p->getNodeId(),
                                                           p->getNodeId(), tp);
                  p->getFileContent()->populateCoreMembers(
                      p->getNodeId(), p->getNodeId(), tpsRef);
                  params->emplace_back(tp);
                  uhdm::ParamAssign* pass = s.make<uhdm::ParamAssign>();
                  pass->setRhs(tp);
                  pass->setLhs(fparam);
                  pass->setParent(ref);
                  pass->setFile(fparam->getFile());
                  pass->setStartLine(fparam->getStartLine());
                  pass->setStartColumn(fparam->getStartColumn());
                  pass->setEndLine(tp->getEndLine());
                  pass->setEndColumn(tp->getEndColumn());
                  assigns->emplace_back(pass);
                } else if (uhdm::Any* exp = compileExpression(
                               component, actualFC, Param_expression,
                               compileDesign, reduce, nullptr, instance)) {
                  if (exp->getUhdmType() == uhdm::UhdmType::RefObj) {
                    const std::string_view name =
                        ((uhdm::RefObj*)exp)->getName();
                    if (uhdm::Typespec* tps = compileDatastructureTypespec(
                            component, actualFC, param, compileDesign, reduce,
                            instance, "", name)) {
                      uhdm::TypeParameter* tp = s.make<uhdm::TypeParameter>();
                      tp->setName(fName);
                      uhdm::RefTypespec* tpsRef = s.make<uhdm::RefTypespec>();
                      tpsRef->setParent(tp);
                      tpsRef->setName(name);
                      tpsRef->setActual(tps);
                      p->getFileContent()->populateCoreMembers(
                          p->getNodeId(), p->getNodeId(), tp);
                      p->getFileContent()->populateCoreMembers(
                          p->getNodeId(), p->getNodeId(), tpsRef);
                      tp->setTypespec(tpsRef);
                      tps->setParent(tp);
                      tp->setParent(ref);
                      params->emplace_back(tp);
                      uhdm::ParamAssign* pass = s.make<uhdm::ParamAssign>();
                      pass->setRhs(tp);
                      pass->setLhs(fparam);
                      pass->setParent(ref);
                      pass->setFile(fparam->getFile());
                      pass->setStartLine(fparam->getStartLine());
                      pass->setStartColumn(fparam->getStartColumn());
                      pass->setEndLine(tp->getEndLine());
                      pass->setEndColumn(tp->getEndColumn());
                      fC->populateCoreMembers(InvalidNodeId, InvalidNodeId,
                                              pass);
                      assigns->emplace_back(pass);
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
      const std::string_view libName = fC->getLibrary()->getName();
      ModuleDefinition* def =
          design->getModuleDefinition(StrCat(libName, "@", typeName));
      if (def) {
        if (def->getType() == VObjectType::paInterface_declaration) {
          uhdm::InterfaceTypespec* tps = s.make<uhdm::InterfaceTypespec>();
          tps->setName(typeName);
          tps->setInterface(def->getUhdmModel<uhdm::Interface>());
          fC->populateCoreMembers(type, type, tps);
          result = tps;
          if (!suffixname.empty()) {
            const DataType* defType = def->getDataType(design, suffixname);
            bool foundDataType = false;
            while (defType) {
              foundDataType = true;
              if (uhdm::Typespec* t = defType->getTypespec()) {
                result = t;
                return result;
              }
              defType = defType->getDefinition();
            }
            if (foundDataType) {
              // The binding to the actual typespec is still incomplete
              result = s.make<uhdm::LogicTypespec>();
              return result;
            }
          }
          if (NodeId sub = fC->Sibling(type)) {
            const std::string_view name = fC->SymName(sub);
            if (def->getModport(name)) {
              uhdm::InterfaceTypespec* mptps =
                  s.make<uhdm::InterfaceTypespec>();
              mptps->setName(name);
              mptps->setInterface(def->getUhdmModel<uhdm::Interface>());
              fC->populateCoreMembers(sub, sub, mptps);
              mptps->setParent(tps);
              mptps->setIsModport(true);
              result = mptps;
            }
          }
        }
      }
    }

    if (result == nullptr) {
      uhdm::UnsupportedTypespec* tps = s.make<uhdm::UnsupportedTypespec>();
      tps->setName(typeName);
      tps->setParent(pscope);
      fC->populateCoreMembers(type, type, tps);
      result = tps;
    }
  } else {
    uhdm::UnsupportedTypespec* tps = s.make<uhdm::UnsupportedTypespec>();
    tps->setName(typeName);
    tps->setParent(pscope);
    fC->populateCoreMembers(type, type, tps);
    result = tps;
  }
  return result;
}

uhdm::TypespecMember* CompileHelper::buildTypespecMember(
    CompileDesign* compileDesign, const FileContent* fC, NodeId id) {
  /*
  std::string hash = fileName + ":" + name + ":" + value + ":" +
  std::to_string(line) + ":" + std::to_string(column) + ":" +
  std::to_string(eline) + ":" + std::to_string(ecolumn);
  std::unordered_map<std::string, uhdm::TypespecMember*>::iterator itr =
      m_cache_typespec_member.find(hash);
  */
  uhdm::Serializer& s = compileDesign->getSerializer();
  uhdm::TypespecMember* var = s.make<uhdm::TypespecMember>();
  var->setName(fC->SymName(id));
  if (NodeId siblingId = fC->Sibling(id)) {
    fC->populateCoreMembers(id, siblingId, var);
  } else {
    fC->populateCoreMembers(id, id, var);
  }
  return var;
}

IntTypespec* CompileHelper::buildIntTypespec(CompileDesign* compileDesign,
                                             PathId fileId,
                                             std::string_view name,
                                             std::string_view value,
                                             uint32_t line, uint16_t column,
                                             uint32_t eline, uint16_t ecolumn) {
  FileSystem* const fileSystem = m_session->getFileSystem();
  /*
  std::string hash = fileName + ":" + name + ":" + value + ":" +
  std::to_string(line)  + ":" + std::to_string(column) + ":" +
  std::to_string(eline) + ":" + std::to_string(ecolumn);
  std::unordered_map<std::string, uhdm::IntTypespec*>::iterator itr =
      m_cache_int_typespec.find(hash);
  */
  uhdm::IntTypespec* var = nullptr;
  // if (itr == m_cache_int_typespec.end()) {
  uhdm::Serializer& s = compileDesign->getSerializer();
  var = s.make<uhdm::IntTypespec>();
  var->setValue(value);
  var->setName(name);
  var->setFile(fileSystem->toPath(fileId));
  var->setStartLine(line);
  var->setStartColumn(column);
  var->setEndLine(eline);
  var->setEndColumn(ecolumn);
  //  m_cache_int_typespec.insert(std::make_pair(hash, var));
  //} else {
  //  var = (*itr).second;
  //}
  return var;
}

uhdm::Typespec* CompileHelper::compileBuiltinTypespec(
    DesignComponent* component, const FileContent* fC, NodeId type,
    VObjectType the_type, CompileDesign* compileDesign,
    uhdm::RangeCollection* ranges, uhdm::Any* pstmt) {
  uhdm::Serializer& s = compileDesign->getSerializer();
  uhdm::Typespec* result = nullptr;
  NodeId sign = fC->Sibling(type);
  // 6.8 Variable declarations
  // The byte, shortint, int, integer, and longint types are signed types by
  // default.
  bool isSigned = true;
  if (sign && (fC->Type(sign) == VObjectType::paSigning_Unsigned)) {
    isSigned = false;
  }
  switch (the_type) {
    case VObjectType::paIntVec_TypeLogic:
    case VObjectType::paIntVec_TypeReg: {
      // 6.8 Variable declarations
      // Other net and variable types can be explicitly declared as signed.
      isSigned = false;
      if (sign && (fC->Type(sign) == VObjectType::paSigning_Signed)) {
        isSigned = true;
      }
      uhdm::LogicTypespec* var = s.make<uhdm::LogicTypespec>();
      var->setSigned(isSigned);
      fC->populateCoreMembers(type, isSigned ? sign : type, var);
      if ((ranges != nullptr) && !ranges->empty()) {
        var->setRanges(ranges);
        for (uhdm::Range* r : *ranges) r->setParent(var, true);
        var->setEndLine(ranges->back()->getEndLine());
        var->setEndColumn(ranges->back()->getEndColumn());
      }
      result = var;
      break;
    }
    case VObjectType::paIntegerAtomType_Int: {
      uhdm::IntTypespec* var = s.make<uhdm::IntTypespec>();
      var->setSigned(isSigned);
      fC->populateCoreMembers(type, isSigned ? type : sign, var);
      result = var;
      break;
    }
    case VObjectType::paIntegerAtomType_Integer: {
      uhdm::IntegerTypespec* var = s.make<uhdm::IntegerTypespec>();
      var->setSigned(isSigned);
      fC->populateCoreMembers(type, isSigned ? type : sign, var);
      result = var;
      break;
    }
    case VObjectType::paIntegerAtomType_Byte: {
      uhdm::ByteTypespec* var = s.make<uhdm::ByteTypespec>();
      var->setSigned(isSigned);
      fC->populateCoreMembers(type, isSigned ? type : sign, var);
      result = var;
      break;
    }
    case VObjectType::paIntegerAtomType_LongInt: {
      uhdm::LongIntTypespec* var = s.make<uhdm::LongIntTypespec>();
      var->setSigned(isSigned);
      fC->populateCoreMembers(type, isSigned ? type : sign, var);
      result = var;
      break;
    }
    case VObjectType::paIntegerAtomType_Shortint: {
      uhdm::ShortIntTypespec* var = s.make<uhdm::ShortIntTypespec>();
      var->setSigned(isSigned);
      fC->populateCoreMembers(type, isSigned ? type : sign, var);
      result = var;
      break;
    }
    case VObjectType::paIntegerAtomType_Time: {
      uhdm::TimeTypespec* var = s.make<uhdm::TimeTypespec>();
      fC->populateCoreMembers(type, type, var);
      result = var;
      break;
    }
    case VObjectType::paIntVec_TypeBit: {
      uhdm::BitTypespec* var = s.make<uhdm::BitTypespec>();
      if ((ranges != nullptr) && !ranges->empty()) {
        var->setRanges(ranges);
        for (uhdm::Range* r : *ranges) r->setParent(var, true);
        var->setEndLine(ranges->back()->getEndLine());
        var->setEndColumn(ranges->back()->getEndColumn());
      }
      isSigned = false;
      if (sign && (fC->Type(sign) == VObjectType::paSigning_Signed)) {
        isSigned = true;
      }
      var->setSigned(isSigned);
      fC->populateCoreMembers(type, isSigned ? sign : type, var);
      result = var;
      break;
    }
    case VObjectType::paNonIntType_ShortReal: {
      uhdm::ShortRealTypespec* var = s.make<uhdm::ShortRealTypespec>();
      fC->populateCoreMembers(type, type, var);
      result = var;
      break;
    }
    case VObjectType::paNonIntType_Real: {
      uhdm::RealTypespec* var = s.make<uhdm::RealTypespec>();
      fC->populateCoreMembers(type, type, var);
      result = var;
      break;
    }
    case VObjectType::paString_type: {
      uhdm::StringTypespec* tps = s.make<uhdm::StringTypespec>();
      fC->populateCoreMembers(type, type, tps);
      result = tps;
      break;
    }
    default:
      uhdm::LogicTypespec* var = s.make<uhdm::LogicTypespec>();
      if ((ranges != nullptr) && !ranges->empty()) {
        var->setRanges(ranges);
        for (uhdm::Range* r : *ranges) r->setParent(var, true);
        var->setEndLine(ranges->back()->getEndLine());
        var->setEndColumn(ranges->back()->getEndColumn());
      }
      fC->populateCoreMembers(type, type, var);
      result = var;
      break;
  }
  result->setParent(pstmt);
  return result;
}

uhdm::Typespec* CompileHelper::compileTypespec(
    DesignComponent* component, const FileContent* fC, NodeId id,
    CompileDesign* compileDesign, Reduce reduce, uhdm::Any* pstmt,
    SURELOG::ValuedComponentI* instance, bool isVariable) {
  SymbolTable* const symbols = m_session->getSymbolTable();
  FileSystem* const fileSystem = m_session->getFileSystem();
  ErrorContainer* const errors = m_session->getErrorContainer();
  Design* const design = compileDesign->getCompiler()->getDesign();

  uhdm::Serializer& s = compileDesign->getSerializer();
  if (pstmt == nullptr) pstmt = component->getUhdmModel();
  if (pstmt == nullptr) pstmt = design->getUhdmDesign();
  NodeId nodeId = id;
  if (fC->Type(id) == VObjectType::paData_type) nodeId = fC->Child(id);
  uhdm::Typespec* result = nullptr;
  NodeId type = nodeId;
  if (fC->Type(type) == VObjectType::paData_type_or_implicit) {
    type = fC->Child(type);
  }
  if (fC->Type(type) == VObjectType::paData_type) {
    if (fC->Child(type)) {
      type = fC->Child(type);
    } else {
      // Implicit type
    }
  }
  if (fC->Type(type) == VObjectType::paVIRTUAL) type = fC->Sibling(type);
  VObjectType the_type = fC->Type(type);
  if (the_type == VObjectType::paData_type_or_implicit) {
    type = fC->Child(type);
    the_type = fC->Type(type);
  }
  if (the_type == VObjectType::paData_type) {
    if (fC->Child(type)) {
      type = fC->Child(type);
      if (fC->Type(type) == VObjectType::paVIRTUAL) type = fC->Sibling(type);
    } else {
      // Implicit type
    }
    the_type = fC->Type(type);
  }
  NodeId Packed_dimension;
  if (the_type == VObjectType::paPacked_dimension) {
    Packed_dimension = type;
  } else if (the_type == VObjectType::slStringConst) {
    // Class parameter or struct reference
    Packed_dimension = fC->Sibling(type);
    if (fC->Type(Packed_dimension) != VObjectType::paPacked_dimension)
      Packed_dimension = InvalidNodeId;
  } else {
    Packed_dimension = fC->Sibling(type);
    if (fC->Type(Packed_dimension) == VObjectType::paData_type_or_implicit) {
      Packed_dimension = fC->Child(Packed_dimension);
    }
  }
  bool isPacked = false;
  if (fC->Type(Packed_dimension) == VObjectType::paPacked_keyword) {
    Packed_dimension = fC->Sibling(Packed_dimension);
    isPacked = true;
  }
  if (fC->Type(Packed_dimension) == VObjectType::paStruct_union_member ||
      fC->Type(Packed_dimension) == VObjectType::slStringConst) {
    Packed_dimension = fC->Sibling(Packed_dimension);
  }

  if (fC->Type(Packed_dimension) == VObjectType::paSigning_Signed ||
      fC->Type(Packed_dimension) == VObjectType::paSigning_Unsigned) {
    Packed_dimension = fC->Sibling(Packed_dimension);
  }
  NodeId Packed_dimensionStartId, Packed_dimensionEndId;
  if (fC->Type(Packed_dimension) == VObjectType::paPacked_dimension) {
    isPacked = true;
    Packed_dimensionStartId = Packed_dimensionEndId = Packed_dimension;
    while (fC->Sibling(Packed_dimensionEndId))
      Packed_dimensionEndId = fC->Sibling(Packed_dimensionEndId);
  }
  int32_t size;
  uhdm::RangeCollection* ranges =
      compileRanges(component, fC, Packed_dimension, compileDesign, reduce,
                    pstmt, instance, size, false);
  switch (the_type) {
    case VObjectType::paConstant_mintypmax_expression:
    case VObjectType::paConstant_primary: {
      return compileTypespec(component, fC, fC->Child(type), compileDesign,
                             reduce, pstmt, instance, false);
    }
    case VObjectType::paSystem_task: {
      if (uhdm::Any* res = compileExpression(component, fC, type, compileDesign,
                                             reduce, pstmt, instance)) {
        uhdm::IntegerTypespec* var = s.make<uhdm::IntegerTypespec>();
        fC->populateCoreMembers(type, type, var);
        result = var;
        if (uhdm::Constant* constant = any_cast<uhdm::Constant*>(res)) {
          var->setValue(constant->getValue());
        } else {
          var->setExpr((uhdm::Expr*)res);
        }
      } else {
        uhdm::UnsupportedTypespec* tps = s.make<uhdm::UnsupportedTypespec>();
        tps->setParent(pstmt);
        fC->populateCoreMembers(type, type, tps);
        result = tps;
      }
      break;
    }
    case VObjectType::paEnum_base_type:
    case VObjectType::paEnum_name_declaration: {
      uhdm::Typespec* baseType = nullptr;
      uint64_t baseSize = 64;
      uhdm::EnumTypespec* en = s.make<uhdm::EnumTypespec>();
      if (the_type == VObjectType::paEnum_base_type) {
        baseType =
            compileTypespec(component, fC, fC->Child(type), compileDesign,
                            reduce, pstmt, instance, isVariable);
        type = fC->Sibling(type);
        bool invalidValue = false;
        baseSize =
            Bits(baseType, invalidValue, component, compileDesign, reduce,
                 instance, fC->getFileId(), baseType->getStartLine(), true);
        uhdm::RefTypespec* baseTypeRef = s.make<uhdm::RefTypespec>();
        baseTypeRef->setParent(en);
        baseTypeRef->setName(fC->SymName(nodeId));
        baseTypeRef->setActual(baseType);
        fC->populateCoreMembers(nodeId, nodeId, baseTypeRef);
        en->setBaseTypespec(baseTypeRef);
      }
      NodeId dataTypeId = nodeId;
      while (dataTypeId && (fC->Type(dataTypeId) != VObjectType::paData_type)) {
        dataTypeId = fC->Parent(dataTypeId);
      }
      en->setName(fC->SymName(nodeId));
      fC->populateCoreMembers(dataTypeId, dataTypeId, en);
      uhdm::EnumConstCollection* econsts = en->getEnumConsts(true);
      NodeId enum_name_declaration = type;
      int32_t val = 0;
      while (enum_name_declaration) {
        NodeId enumNameId = fC->Child(enum_name_declaration);
        const std::string_view enumName = fC->SymName(enumNameId);
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
            new Variable(nullptr, fC, enumValueId, InvalidNodeId, enumName);
        if (component) component->addVariable(variable);

        uhdm::EnumConst* econst = s.make<uhdm::EnumConst>();
        econst->setName(enumName);
        econst->setParent(en);
        fC->populateCoreMembers(enum_name_declaration, enum_name_declaration,
                                econst);
        econst->setValue(value->uhdmValue());
        if (enumValueId) {
          uhdm::Any* exp =
              compileExpression(component, fC, enumValueId, compileDesign,
                                Reduce::No, pstmt, nullptr);
          uhdm::ExprEval eval;
          econst->setDecompile(eval.prettyPrint(exp));
        } else {
          econst->setDecompile(value->decompiledValue());
        }
        econst->setSize(value->getSize());
        econsts->emplace_back(econst);
        enum_name_declaration = fC->Sibling(enum_name_declaration);
      }
      result = en;
      break;
    }
    case VObjectType::paInterface_identifier: {
      uhdm::InterfaceTypespec* tps = s.make<uhdm::InterfaceTypespec>();
      const std::string_view name = fC->SymName(type);
      tps->setName(name);
      fC->populateCoreMembers(type, type, tps);
      const std::string_view libName = fC->getLibrary()->getName();
      if (ModuleDefinition* const def =
              design->getModuleDefinition(StrCat(libName, "@", name))) {
        tps->setInterface(def->getUhdmModel<uhdm::Interface>());
      }
      result = tps;
      break;
    }
    case VObjectType::paSigning_Signed: {
      if (m_elaborate == Elaborate::Yes) {
        if (isVariable) {
          // 6.8 Variable declarations, implicit type
          uhdm::LogicTypespec* tps = s.make<uhdm::LogicTypespec>();
          tps->setSigned(true);
          if ((ranges != nullptr) && !ranges->empty()) {
            tps->setRanges(ranges);
            for (uhdm::Range* r : *ranges) r->setParent(tps, true);
            tps->setEndLine(ranges->back()->getEndLine());
            tps->setEndColumn(ranges->back()->getEndColumn());
          }
          result = tps;
        } else {
          // Parameter implicit type is int
          uhdm::IntTypespec* tps = s.make<uhdm::IntTypespec>();
          tps->setSigned(true);
          fC->populateCoreMembers(type, type, tps);
          if ((ranges != nullptr) && !ranges->empty()) {
            tps->setRanges(ranges);
            for (uhdm::Range* r : *ranges) r->setParent(tps, true);
            tps->setEndLine(ranges->back()->getEndLine());
            tps->setEndColumn(ranges->back()->getEndColumn());
          }
          result = tps;
        }
      }
      break;
    }
    case VObjectType::paSigning_Unsigned: {
      if (m_elaborate == Elaborate::Yes) {
        if (isVariable) {
          // 6.8 Variable declarations, implicit type
          uhdm::LogicTypespec* tps = s.make<uhdm::LogicTypespec>();
          if ((ranges != nullptr) && !ranges->empty()) {
            tps->setRanges(ranges);
            for (uhdm::Range* r : *ranges) r->setParent(tps, true);
            tps->setEndLine(ranges->back()->getEndLine());
            tps->setEndColumn(ranges->back()->getEndColumn());
          }
          result = tps;
        } else {
          // Parameter implicit type is int
          uhdm::IntTypespec* tps = s.make<uhdm::IntTypespec>();
          if ((ranges != nullptr) && !ranges->empty()) {
            tps->setRanges(ranges);
            for (uhdm::Range* r : *ranges) r->setParent(tps, true);
            tps->setEndLine(ranges->back()->getEndLine());
            tps->setEndColumn(ranges->back()->getEndColumn());
          }
          result = tps;
        }
      }
      break;
    }
    case VObjectType::paPacked_dimension: {
      if (m_elaborate == Elaborate::Yes) {
        if (isVariable) {
          // 6.8 Variable declarations, implicit type
          uhdm::LogicTypespec* tps = s.make<uhdm::LogicTypespec>();
          if ((ranges != nullptr) && !ranges->empty()) {
            tps->setRanges(ranges);
            for (uhdm::Range* r : *ranges) r->setParent(tps, true);
            tps->setEndLine(ranges->back()->getEndLine());
            tps->setEndColumn(ranges->back()->getEndColumn());
          }
          result = tps;
        } else {
          // Parameter implicit type is bit
          uhdm::IntTypespec* tps = s.make<uhdm::IntTypespec>();
          if ((ranges != nullptr) && !ranges->empty()) {
            tps->setRanges(ranges);
            for (uhdm::Range* r : *ranges) r->setParent(tps, true);
            tps->setEndLine(ranges->back()->getEndLine());
            tps->setEndColumn(ranges->back()->getEndColumn());
          }
          result = tps;
        }
        fC->populateCoreMembers(type, type, result);
      }
      break;
    }
    case VObjectType::paExpression: {
      NodeId Primary = fC->Child(type);
      NodeId Primary_literal = fC->Child(Primary);
      NodeId Name = fC->Child(Primary_literal);
      if (fC->Type(Name) == VObjectType::paClass_scope) {
        return compileTypespec(component, fC, Name, compileDesign, reduce,
                               pstmt, instance, isVariable);
      }
      if (instance) {
        const std::string_view name = fC->SymName(Name);
        result = (uhdm::Typespec*)bindTypespec(design, name, instance, s);
      }
      break;
    }
    case VObjectType::paPrimary_literal: {
      NodeId literal = fC->Child(type);
      if (fC->Type(literal) == VObjectType::slStringConst) {
        const std::string_view typeName = fC->SymName(literal);
        result = compileDatastructureTypespec(
            component, fC, type, compileDesign, reduce, instance, "", typeName);
      } else {
        uhdm::IntegerTypespec* var = s.make<uhdm::IntegerTypespec>();
        var->setValue(StrCat("INT:", fC->SymName(literal)));
        fC->populateCoreMembers(type, type, var);
        result = var;
      }
      break;
    }
    case VObjectType::paIntVec_TypeLogic:
    case VObjectType::paNetType_Wire:
    case VObjectType::paNetType_Supply0:
    case VObjectType::paNetType_Supply1:
    case VObjectType::paNetType_Tri0:
    case VObjectType::paNetType_Tri1:
    case VObjectType::paNetType_Tri:
    case VObjectType::paNetType_TriAnd:
    case VObjectType::paNetType_TriOr:
    case VObjectType::paNetType_TriReg:
    case VObjectType::paNetType_Uwire:
    case VObjectType::paNetType_Wand:
    case VObjectType::paNetType_Wor:
    case VObjectType::paIntVec_TypeReg:
    case VObjectType::paIntegerAtomType_Int:
    case VObjectType::paIntegerAtomType_Integer:
    case VObjectType::paIntegerAtomType_Byte:
    case VObjectType::paIntegerAtomType_LongInt:
    case VObjectType::paIntegerAtomType_Shortint:
    case VObjectType::paIntegerAtomType_Time:
    case VObjectType::paIntVec_TypeBit:
    case VObjectType::paNonIntType_ShortReal:
    case VObjectType::paNonIntType_Real:
    case VObjectType::paString_type: {
      result = compileBuiltinTypespec(component, fC, type, the_type,
                                      compileDesign, ranges, pstmt);
      break;
    }
    case VObjectType::paPackage_scope:
    case VObjectType::paClass_scope: {
      std::string typeName;
      NodeId class_type = fC->Child(type);
      NodeId class_name;
      if (the_type == VObjectType::paClass_scope)
        class_name = fC->Child(class_type);
      else
        class_name = class_type;
      typeName = fC->SymName(class_name);
      std::string packageName = typeName;
      typeName += "::";
      NodeId symb_id = fC->Sibling(type);
      const std::string_view name = fC->SymName(symb_id);
      typeName += name;
      Package* pack = design->getPackage(packageName);
      if (pack) {
        const DataType* dtype = pack->getDataType(design, name);
        if (dtype == nullptr) {
          ClassDefinition* classDefn = pack->getClassDefinition(name);
          dtype = (const DataType*)classDefn;
          if (dtype) {
            uhdm::ClassTypespec* ref = s.make<uhdm::ClassTypespec>();
            ref->setClassDefn(classDefn->getUhdmModel<uhdm::ClassDefn>());
            ref->setName(typeName);
            fC->populateCoreMembers(type, type, ref);
            result = ref;
            break;
          }
        }
        while (dtype) {
          const TypeDef* typed = datatype_cast<TypeDef>(dtype);
          if (typed) {
            const DataType* dt = typed->getDataType();
            if (const Enum* en = datatype_cast<Enum>(dt)) {
              result = en->getTypespec();
            } else if (const Struct* st = datatype_cast<Struct>(dt)) {
              result = st->getTypespec();
            } else if (const Union* un = datatype_cast<Union>(dt)) {
              result = un->getTypespec();
            } else if (const SimpleType* sit = datatype_cast<SimpleType>(dt)) {
              result = sit->getTypespec();
            } else if (const DummyType* sit = datatype_cast<DummyType>(dt)) {
              result = sit->getTypespec();
            }
          }
          dtype = dtype->getDefinition();
          if (result) {
            break;
          }
        }
        if (!result) {
          uhdm::ParamAssignCollection* param_assigns = pack->getParamAssigns();
          if (param_assigns) {
            for (uhdm::ParamAssign* param : *param_assigns) {
              const std::string_view param_name = param->getLhs()->getName();
              if (param_name == name) {
                const uhdm::Any* rhs = param->getRhs();
                if (const uhdm::Expr* exp = any_cast<const uhdm::Expr*>(rhs)) {
                  uhdm::IntTypespec* its = s.make<uhdm::IntTypespec>();
                  its->setValue(exp->getValue());
                  result = its;
                } else {
                  result = (uhdm::Typespec*)rhs;
                }
                break;
              }
            }
          }
        }
        if (ranges && result) {
          if ((result->getUhdmType() != uhdm::UhdmType::LogicTypespec) &&
              (result->getUhdmType() != uhdm::UhdmType::BitTypespec) &&
              (result->getUhdmType() != uhdm::UhdmType::IntTypespec)) {
            uhdm::RefTypespec* resultRef = s.make<uhdm::RefTypespec>();
            fC->populateCoreMembers(type, type, resultRef);
            resultRef->setActual(result);
            if (isPacked) {
              uhdm::PackedArrayTypespec* pats =
                  s.make<uhdm::PackedArrayTypespec>();
              pats->setElemTypespec(resultRef);
              resultRef->setParent(pats);
              if (ranges != nullptr) {
                pats->setRanges(ranges);
                for (uhdm::Range* r : *ranges) r->setParent(pats, true);
              }
              fC->populateCoreMembers(Packed_dimensionStartId,
                                      Packed_dimensionEndId, pats);
              result = pats;
            } else {
              uhdm::ArrayTypespec* pats = s.make<uhdm::ArrayTypespec>();
              pats->setElemTypespec(resultRef);
              resultRef->setParent(pats);
              if (ranges != nullptr) {
                pats->setRanges(ranges);
                for (uhdm::Range* r : *ranges) r->setParent(pats, true);
              }
              result = pats;
            }
            fC->populateCoreMembers(Packed_dimension, Packed_dimension, result);
          }
        }
      }
      if (result == nullptr) {
        uhdm::UnsupportedTypespec* ref = s.make<uhdm::UnsupportedTypespec>();
        ref->setParent(pstmt);
        ref->setPacked(isPacked);
        ref->setName(typeName);
        fC->populateCoreMembers(id, id, ref);
        if (ranges != nullptr) {
          ref->setRanges(ranges);
          for (uhdm::Range* r : *ranges) r->setParent(ref, true);
        }
        result = ref;
      }
      break;
    }
    case VObjectType::paStruct_union: {
      NodeId struct_or_union = fC->Child(type);
      VObjectType struct_or_union_type = fC->Type(struct_or_union);
      uhdm::TypespecMemberCollection* members =
          s.makeCollection<uhdm::TypespecMember>();

      NodeId struct_or_union_member = fC->Sibling(type);
      if (fC->Type(struct_or_union_member) == VObjectType::paPacked_keyword) {
        struct_or_union_member = fC->Sibling(struct_or_union_member);
        isPacked = true;
      }

      uhdm::Typespec* structOtUnionTypespec = nullptr;
      if (struct_or_union_type == VObjectType::paStruct_keyword) {
        uhdm::StructTypespec* ts = s.make<uhdm::StructTypespec>();
        ts->setPacked(isPacked);
        ts->setMembers(members);
        result = structOtUnionTypespec = ts;
      } else {
        uhdm::UnionTypespec* ts = s.make<uhdm::UnionTypespec>();
        ts->setPacked(isPacked);
        ts->setMembers(members);
        result = structOtUnionTypespec = ts;
      }
      result->setParent(pstmt);
      fC->populateCoreMembers(id, id, result);

      if (ranges) {
        structOtUnionTypespec->setEndLine(fC->Line(Packed_dimensionStartId));
        structOtUnionTypespec->setEndColumn(
            fC->Column(Packed_dimensionStartId) - 1);

        uhdm::RefTypespec* resultRef = s.make<uhdm::RefTypespec>();
        resultRef->setActual(result);
        fC->populateCoreMembers(id, InvalidNodeId, resultRef);
        resultRef->setEndLine(fC->Line(Packed_dimensionStartId));
        resultRef->setEndColumn(fC->Column(Packed_dimensionStartId) - 1);
        if (isPacked) {
          uhdm::PackedArrayTypespec* pats = s.make<uhdm::PackedArrayTypespec>();
          pats->setElemTypespec(resultRef);
          if (ranges != nullptr) {
            pats->setRanges(ranges);
            for (uhdm::Range* r : *ranges) r->setParent(pats, true);
          }
          resultRef->setParent(pats);
          result = pats;
        } else {
          uhdm::ArrayTypespec* pats = s.make<uhdm::ArrayTypespec>();
          pats->setElemTypespec(resultRef);
          if (ranges != nullptr) {
            pats->setRanges(ranges);
            for (uhdm::Range* r : *ranges) r->setParent(pats, true);
          }
          resultRef->setParent(pats);
          result = pats;
        }
        fC->populateCoreMembers(Packed_dimensionStartId, Packed_dimensionEndId,
                                result);
      }

      while (struct_or_union_member) {
        NodeId Data_type_or_void = fC->Child(struct_or_union_member);
        NodeId Data_type = fC->Child(Data_type_or_void);
        NodeId List_of_variable_decl_assignments =
            fC->Sibling(Data_type_or_void);
        NodeId Variable_decl_assignment =
            fC->Child(List_of_variable_decl_assignments);
        while (Variable_decl_assignment) {
          uhdm::Typespec* member_ts = nullptr;
          if (Data_type) {
            member_ts = compileTypespec(component, fC, Data_type, compileDesign,
                                        reduce, result, instance, false);
          } else {
            uhdm::VoidTypespec* tps = s.make<uhdm::VoidTypespec>();
            tps->setParent(result);
            fC->populateCoreMembers(Data_type_or_void, Data_type_or_void, tps);
            member_ts = tps;
          }
          NodeId member_name = fC->Child(Variable_decl_assignment);
          NodeId Expression = fC->Sibling(member_name);
          uhdm::TypespecMember* m =
              buildTypespecMember(compileDesign, fC, member_name);
          m->setParent(structOtUnionTypespec);
          if (member_ts != nullptr) {
            if (m->getTypespec() == nullptr) {
              uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
              tsRef->setParent(m);
              tsRef->setName(fC->SymName(Data_type));
              fC->populateCoreMembers(Data_type_or_void, Data_type_or_void,
                                      tsRef);
              m->setTypespec(tsRef);
            }
            m->getTypespec()->setActual(member_ts);
          }
          if (Expression &&
              (fC->Type(Expression) != VObjectType::paVariable_dimension)) {
            if (uhdm::Any* ex =
                    compileExpression(component, fC, Expression, compileDesign,
                                      reduce, m, instance, false)) {
              m->setDefaultValue((uhdm::Expr*)ex);
            }
          }
          if (Expression &&
              (fC->Type(Expression) == VObjectType::paVariable_dimension)) {
            NodeId Unpacked_dimension = fC->Child(Expression);
            if (fC->Type(Unpacked_dimension) ==
                VObjectType::paUnpacked_dimension) {
              int32_t size;
              uhdm::RangeCollection* ranges = compileRanges(
                  component, fC, Unpacked_dimension, compileDesign, reduce,
                  nullptr, instance, size, false);
              uhdm::ArrayTypespec* pats = s.make<uhdm::ArrayTypespec>();
              uhdm::RefTypespec* ref = s.make<uhdm::RefTypespec>();
              if (isPacked) {
                Location loc1(
                    fC->getFileId(), fC->Line(Unpacked_dimension),
                    fC->Column(Unpacked_dimension),
                    symbols->registerSymbol(fC->SymName(member_name)));
                Error err(ErrorDefinition::COMP_UNPACKED_IN_PACKED, loc1);
                errors->addError(err);
              }
              pats->setElemTypespec(ref);
              pats->setParent(m);
              fC->populateCoreMembers(Unpacked_dimension, Unpacked_dimension,
                                      pats);
              ref->setParent(pats);
              fC->populateCoreMembers(Data_type, Data_type, ref);
              ref->setActual(m->getTypespec()->getActual());
              m->getTypespec()->setActual(pats);
              if (ranges != nullptr) {
                pats->setRanges(ranges);
                for (auto r : *ranges) r->setParent(pats, true);
              }
            }
          }
          members->emplace_back(m);
          Variable_decl_assignment = fC->Sibling(Variable_decl_assignment);
        }
        struct_or_union_member = fC->Sibling(struct_or_union_member);
      }
      break;
    }
    case VObjectType::paSimple_type:
    case VObjectType::paPs_type_identifier:
    case VObjectType::paInteger_type: {
      return compileTypespec(component, fC, fC->Child(type), compileDesign,
                             reduce, pstmt, instance, false);
    }
    case VObjectType::slStringConst: {
      const std::string_view typeName = fC->SymName(type);
      if (typeName == "logic") {
        uhdm::LogicTypespec* var = s.make<uhdm::LogicTypespec>();
        if ((ranges != nullptr) && !ranges->empty()) {
          var->setRanges(ranges);
          for (uhdm::Range* r : *ranges) r->setParent(var, true);
          var->setEndLine(ranges->back()->getEndLine());
          var->setEndColumn(ranges->back()->getEndColumn());
        }
        fC->populateCoreMembers(type, type, var);
        result = var;
      } else if (typeName == "bit") {
        uhdm::BitTypespec* var = s.make<uhdm::BitTypespec>();
        if ((ranges != nullptr) && !ranges->empty()) {
          var->setRanges(ranges);
          for (uhdm::Range* r : *ranges) r->setParent(var, true);
          var->setEndLine(ranges->back()->getEndLine());
          var->setEndColumn(ranges->back()->getEndColumn());
        }
        fC->populateCoreMembers(type, type, var);
        result = var;
      } else if (typeName == "byte") {
        uhdm::ByteTypespec* var = s.make<uhdm::ByteTypespec>();
        fC->populateCoreMembers(type, type, var);
        result = var;
      } else if ((m_reduce == Reduce::Yes) && (reduce == Reduce::Yes)) {
        if (uhdm::Any* cast_to =
                getValue(typeName, component, compileDesign,
                         reduce == Reduce::Yes ? Reduce::No : Reduce::Yes,
                         instance, fC->getFileId(), fC->Line(type), nullptr)) {
          uhdm::Constant* c = any_cast<uhdm::Constant>(cast_to);
          if (c) {
            uhdm::IntegerTypespec* var = s.make<uhdm::IntegerTypespec>();
            var->setValue(c->getValue());
            fC->populateCoreMembers(type, type, var);
            result = var;
          } else {
            uhdm::VoidTypespec* tps = s.make<uhdm::VoidTypespec>();
            fC->populateCoreMembers(type, type, tps);
            result = tps;
          }
        }
      }
      if (!result) {
        while (instance) {
          if (ModuleInstance* inst =
                  valuedcomponenti_cast<ModuleInstance*>(instance)) {
            if (inst->getNetlist()) {
              uhdm::ParamAssignCollection* param_assigns =
                  inst->getNetlist()->param_assigns();
              if (param_assigns) {
                for (uhdm::ParamAssign* param : *param_assigns) {
                  const std::string_view param_name =
                      param->getLhs()->getName();
                  if (param_name == typeName) {
                    const uhdm::Any* rhs = param->getRhs();
                    if (const uhdm::Constant* exp =
                            any_cast<const uhdm::Constant*>(rhs)) {
                      uhdm::IntTypespec* its = buildIntTypespec(
                          compileDesign,
                          fileSystem->toPathId(param->getFile(), symbols),
                          typeName, exp->getValue(), param->getStartLine(),
                          param->getStartColumn(), param->getStartLine(),
                          param->getStartColumn());
                      result = its;
                    } else {
                      uhdm::Any* ex =
                          compileExpression(component, fC, type, compileDesign,
                                            Reduce::No, pstmt, instance, false);
                      if (ex) {
                        uhdm::HierPath* path = nullptr;
                        if (ex->getUhdmType() == uhdm::UhdmType::HierPath) {
                          path = (uhdm::HierPath*)ex;
                        } else if (ex->getUhdmType() ==
                                   uhdm::UhdmType::RefObj) {
                          path = s.make<uhdm::HierPath>();
                          uhdm::RefObj* ref = s.make<uhdm::RefObj>();
                          ref->setName(typeName);
                          ref->setParent(path);
                          fC->populateCoreMembers(type, type, ref);
                          path->getPathElems(true)->emplace_back(ref);
                        }
                        if (path) {
                          bool invalidValue = false;
                          result = (uhdm::Typespec*)decodeHierPath(
                              path, invalidValue, component, compileDesign,
                              reduce, instance, fC->getFileId(), fC->Line(type),
                              nullptr, false, true);
                        }
                      }
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
      if (!result && component) {
        if (uhdm::ParamAssignCollection* param_assigns =
                component->getParamAssigns()) {
          for (uhdm::ParamAssign* param : *param_assigns) {
            const std::string_view param_name = param->getLhs()->getName();
            if (param_name == typeName) {
              const uhdm::Any* rhs = param->getRhs();
              if (const uhdm::Constant* exp =
                      any_cast<const uhdm::Constant*>(rhs)) {
                uhdm::IntTypespec* its = buildIntTypespec(
                    compileDesign,
                    fileSystem->toPathId(param->getFile(), symbols), typeName,
                    exp->getValue(), param->getStartLine(),
                    param->getStartColumn(), param->getStartLine(),
                    param->getStartColumn());
                result = its;
              } else if (const uhdm::Operation* exp =
                             any_cast<const uhdm::Operation*>(rhs)) {
                if (const uhdm::RefTypespec* rt = exp->getTypespec())
                  result = const_cast<uhdm::Typespec*>(rt->getActual());
              }
              break;
            }
          }
        }
      }
      if (!result) {
        if (component) {
          ClassDefinition* cl = design->getClassDefinition(typeName);
          if (cl == nullptr) {
            cl = design->getClassDefinition(
                StrCat(component->getName(), "::", typeName));
          }
          if (cl == nullptr) {
            if (const DesignComponent* p =
                    valuedcomponenti_cast<const DesignComponent*>(
                        component->getParentScope())) {
              cl = design->getClassDefinition(
                  StrCat(p->getName(), "::", typeName));
            }
          }
          if (cl) {
            uhdm::ClassTypespec* tps = s.make<uhdm::ClassTypespec>();
            tps->setName(typeName);
            tps->setParent(pstmt);
            tps->setClassDefn(cl->getUhdmModel<uhdm::ClassDefn>());
            fC->populateCoreMembers(type, type, tps);
            result = tps;
          }
        }
      }
      if (result == nullptr) {
        result = compileDatastructureTypespec(
            component, fC, type, compileDesign, reduce, instance, "", typeName);
        if (ranges && result) {
          uhdm::UhdmType dstype = result->getUhdmType();
          uhdm::RefTypespec* resultRef = s.make<uhdm::RefTypespec>();
          resultRef->setName(typeName);
          resultRef->setActual(result);
          uhdm::Typespec* result2 = nullptr;
          if (dstype == uhdm::UhdmType::StructTypespec ||
              dstype == uhdm::UhdmType::EnumTypespec ||
              dstype == uhdm::UhdmType::UnionTypespec) {
            uhdm::PackedArrayTypespec* pats =
                s.make<uhdm::PackedArrayTypespec>();
            pats->setParent(pstmt);
            pats->setElemTypespec(resultRef);
            pats->setRanges(ranges);
            result2 = pats;
          } else if (dstype == uhdm::UhdmType::LogicTypespec) {
            uhdm::LogicTypespec* pats = s.make<uhdm::LogicTypespec>();
            pats->setParent(pstmt);
            pats->setElemTypespec(resultRef);
            pats->setRanges(ranges);
            result2 = pats;
          } else if (dstype == uhdm::UhdmType::ArrayTypespec ||
                     dstype == uhdm::UhdmType::InterfaceTypespec) {
            uhdm::ArrayTypespec* pats = s.make<uhdm::ArrayTypespec>();
            pats->setParent(pstmt);
            pats->setElemTypespec(resultRef);
            pats->setRanges(ranges);
            result2 = pats;
          } else if (dstype == uhdm::UhdmType::PackedArrayTypespec) {
            uhdm::PackedArrayTypespec* pats =
                s.make<uhdm::PackedArrayTypespec>();
            pats->setParent(pstmt);
            pats->setElemTypespec(resultRef);
            pats->setRanges(ranges);
            result2 = pats;
          }
          if (result2 != nullptr) {
            fC->populateCoreMembers(Packed_dimensionStartId,
                                    Packed_dimensionEndId, result2);
            result2->setEndLine(ranges->back()->getEndLine());
            result2->setEndColumn(ranges->back()->getEndColumn());
            for (uhdm::Range* r : *ranges) r->setParent(result2, true);
            result = result2;
          }
          resultRef->setParent(result);
          fC->populateCoreMembers(type, type, resultRef);
        }
        if (result) {
          fC->populateCoreMembers(type, type, result);
        }
      }
      if ((!result) && component) {
        if (uhdm::AnyCollection* params = component->getParameters()) {
          for (uhdm::Any* param : *params) {
            if ((param->getUhdmType() == uhdm::UhdmType::TypeParameter) &&
                (param->getName() == typeName)) {
              result = (uhdm::Typespec*)param;
              break;
            }
          }
        }
      }

      break;
    }
    case VObjectType::paConstant_expression: {
      if (uhdm::Expr* exp = (uhdm::Expr*)compileExpression(
              component, fC, type, compileDesign, reduce, pstmt, instance,
              reduce == Reduce::No)) {
        if (exp->getUhdmType() == uhdm::UhdmType::RefObj) {
          return compileTypespec(component, fC, fC->Child(type), compileDesign,
                                 reduce, result, instance, false);
        } else {
          uhdm::IntegerTypespec* var = s.make<uhdm::IntegerTypespec>();
          if (exp->getUhdmType() == uhdm::UhdmType::Constant) {
            var->setValue(exp->getValue());
          } else {
            var->setExpr(exp);
            exp->setParent(var, true);
          }
          fC->populateCoreMembers(type, type, var);
          result = var;
        }
      }
      break;
    }
    case VObjectType::paChandle_type: {
      uhdm::ChandleTypespec* tps = s.make<uhdm::ChandleTypespec>();
      fC->populateCoreMembers(type, type, tps);
      result = tps;
      break;
    }
    case VObjectType::paConstant_range: {
      uhdm::LogicTypespec* tps = s.make<uhdm::LogicTypespec>();
      fC->populateCoreMembers(type, type, tps);
      if (uhdm::RangeCollection* ranges =
              compileRanges(component, fC, type, compileDesign, reduce, tps,
                            instance, size, false)) {
        if (!ranges->empty()) {
          tps->setRanges(ranges);
          for (uhdm::Range* r : *ranges) r->setParent(tps, true);
          tps->setEndLine(ranges->back()->getEndLine());
          tps->setEndColumn(ranges->back()->getEndColumn());
        }
      }
      result = tps;
      break;
    }
    case VObjectType::paEvent_type: {
      uhdm::EventTypespec* tps = s.make<uhdm::EventTypespec>();
      fC->populateCoreMembers(type, type, tps);
      result = tps;
      break;
    }
    case VObjectType::paNonIntType_RealTime: {
      uhdm::TimeTypespec* tps = s.make<uhdm::TimeTypespec>();
      fC->populateCoreMembers(type, type, tps);
      result = tps;
      break;
    }
    case VObjectType::paType_reference: {
      NodeId child = fC->Child(type);
      if (fC->Type(child) == VObjectType::paExpression) {
        uhdm::Expr* exp = (uhdm::Expr*)compileExpression(
            component, fC, child, compileDesign, reduce, nullptr, instance,
            reduce == Reduce::Yes);
        if (exp) {
          uhdm::UhdmType typ = exp->getUhdmType();
          if (typ == uhdm::UhdmType::RefObj) {
            return compileTypespec(component, fC, child, compileDesign, reduce,
                                   result, instance, false);
          } else if (typ == uhdm::UhdmType::Constant) {
            uhdm::Constant* c = (uhdm::Constant*)exp;
            int32_t ctype = c->getConstType();
            if (ctype == vpiIntConst || ctype == vpiDecConst) {
              uhdm::IntTypespec* tps = s.make<uhdm::IntTypespec>();
              tps->setSigned(true);
              result = tps;
            } else if (ctype == vpiUIntConst || ctype == vpiBinaryConst ||
                       ctype == vpiHexConst || ctype == vpiOctConst) {
              uhdm::IntTypespec* tps = s.make<uhdm::IntTypespec>();
              result = tps;
            } else if (ctype == vpiRealConst) {
              uhdm::RealTypespec* tps = s.make<uhdm::RealTypespec>();
              result = tps;
            } else if (ctype == vpiStringConst) {
              uhdm::StringTypespec* tps = s.make<uhdm::StringTypespec>();
              result = tps;
            } else if (ctype == vpiTimeConst) {
              uhdm::TimeTypespec* tps = s.make<uhdm::TimeTypespec>();
              result = tps;
            }
            fC->populateCoreMembers(type, type, result);
          }
        } else {
          std::string lineText;
          fileSystem->readLine(fC->getFileId(), fC->Line(type), lineText);
          Location loc(fC->getFileId(type), fC->Line(type), fC->Column(type),
                       symbols->registerSymbol(
                           StrCat("<", fC->printObject(type), "> ", lineText)));
          Error err(ErrorDefinition::UHDM_UNSUPPORTED_TYPE, loc);
          errors->addError(err);
        }
      } else {
        return compileTypespec(component, fC, child, compileDesign, reduce,
                               result, instance, false);
      }
      break;
    }
    case VObjectType::paData_type_or_implicit: {
      uhdm::LogicTypespec* tps = s.make<uhdm::LogicTypespec>();
      fC->populateCoreMembers(type, type, tps);
      if (uhdm::RangeCollection* ranges =
              compileRanges(component, fC, type, compileDesign, reduce, tps,
                            instance, size, false)) {
        if (!ranges->empty()) {
          tps->setRanges(ranges);
          for (uhdm::Range* r : *ranges) r->setParent(tps, true);
          tps->setEndLine(ranges->back()->getEndLine());
          tps->setEndColumn(ranges->back()->getEndColumn());
        }
      }
      result = tps;
      break;
    }
    case VObjectType::paImplicit_data_type: {
      // Interconnect
      uhdm::LogicTypespec* tps = s.make<uhdm::LogicTypespec>();
      fC->populateCoreMembers(type, type, tps);
      if (uhdm::RangeCollection* ranges =
              compileRanges(component, fC, fC->Child(type), compileDesign,
                            reduce, tps, instance, size, false)) {
        if (!ranges->empty()) {
          tps->setRanges(ranges);
          for (uhdm::Range* r : *ranges) r->setParent(tps, true);
          tps->setEndLine(ranges->back()->getEndLine());
          tps->setEndColumn(ranges->back()->getEndColumn());
        }
      }
      result = tps;
      break;
    }
    default:
      if (type) {
        std::string lineText;
        fileSystem->readLine(fC->getFileId(), fC->Line(type), lineText);
        Location loc(fC->getFileId(type), fC->Line(type), fC->Column(type),
                     symbols->registerSymbol(
                         StrCat("<", fC->printObject(type), "> ", lineText)));
        Error err(ErrorDefinition::UHDM_UNSUPPORTED_TYPE, loc);
        errors->addError(err);
      }
      break;
  };
  if (result) {
    if ((m_elaborate == Elaborate::Yes) && component &&
        !result->getInstance()) {
      result->setInstance(component->getUhdmModel<uhdm::Instance>());
    }
    if (component->getUhdmModel() != nullptr) {
      result->setParent(component->getUhdmModel());
    }
  }
  return result;
}

uhdm::Typespec* CompileHelper::elabTypespec(DesignComponent* component,
                                            uhdm::Typespec* spec,
                                            CompileDesign* compileDesign,
                                            uhdm::Any* pexpr,
                                            ValuedComponentI* instance) {
  SymbolTable* const symbols = m_session->getSymbolTable();
  FileSystem* const fileSystem = m_session->getFileSystem();

  uhdm::Serializer& s = compileDesign->getSerializer();
  uhdm::Typespec* result = spec;
  uhdm::UhdmType type = spec->getUhdmType();
  uhdm::RangeCollection* ranges = nullptr;
  switch (type) {
    case uhdm::UhdmType::BitTypespec: {
      uhdm::BitTypespec* tps = (uhdm::BitTypespec*)spec;
      ranges = tps->getRanges();
      if (ranges) {
        uhdm::ElaboratorContext elaboratorContext(&s, false, true);
        uhdm::BitTypespec* res = any_cast<uhdm::BitTypespec>(
            uhdm::clone_tree((uhdm::Any*)spec, &elaboratorContext));
        ranges = res->getRanges();
        result = res;
      }
      break;
    }
    case uhdm::UhdmType::LogicTypespec: {
      uhdm::LogicTypespec* tps = (uhdm::LogicTypespec*)spec;
      ranges = tps->getRanges();
      if (ranges) {
        uhdm::ElaboratorContext elaboratorContext(&s, false, true);
        uhdm::LogicTypespec* res = any_cast<uhdm::LogicTypespec>(
            uhdm::clone_tree((uhdm::Any*)spec, &elaboratorContext));
        ranges = res->getRanges();
        result = res;
      }
      break;
    }
    case uhdm::UhdmType::ArrayTypespec: {
      uhdm::ArrayTypespec* tps = (uhdm::ArrayTypespec*)spec;
      ranges = tps->getRanges();
      if (ranges) {
        uhdm::ElaboratorContext elaboratorContext(&s, false, true);
        uhdm::ArrayTypespec* res = any_cast<uhdm::ArrayTypespec>(
            uhdm::clone_tree((uhdm::Any*)spec, &elaboratorContext));
        ranges = res->getRanges();
        result = res;
      }
      break;
    }
    case uhdm::UhdmType::PackedArrayTypespec: {
      uhdm::PackedArrayTypespec* tps = (uhdm::PackedArrayTypespec*)spec;
      ranges = tps->getRanges();
      if (ranges) {
        uhdm::ElaboratorContext elaboratorContext(&s, false, true);
        uhdm::PackedArrayTypespec* res = any_cast<uhdm::PackedArrayTypespec>(
            uhdm::clone_tree((uhdm::Any*)spec, &elaboratorContext));
        ranges = res->getRanges();
        result = res;
      }
      break;
    }
    default:
      break;
  }
  if ((m_reduce == Reduce::Yes) && ranges) {
    for (uhdm::Range* oldRange : *ranges) {
      uhdm::Expr* oldLeft = oldRange->getLeftExpr();
      uhdm::Expr* oldRight = oldRange->getRightExpr();
      bool invalidValue = false;
      uhdm::Expr* newLeft =
          reduceExpr(oldLeft, invalidValue, component, compileDesign, instance,
                     fileSystem->toPathId(oldLeft->getFile(), symbols),
                     oldLeft->getStartLine(), pexpr);
      uhdm::Expr* newRight =
          reduceExpr(oldRight, invalidValue, component, compileDesign, instance,
                     fileSystem->toPathId(oldRight->getFile(), symbols),
                     oldRight->getStartLine(), pexpr);
      if (!invalidValue) {
        oldRange->setLeftExpr(newLeft);
        oldRange->setRightExpr(newRight);
      }
    }
  }
  return result;
}

bool CompileHelper::isOverloaded(const uhdm::Any* expr,
                                 CompileDesign* compileDesign,
                                 ValuedComponentI* instance) {
  if (instance == nullptr) return false;
  ModuleInstance* inst = valuedcomponenti_cast<ModuleInstance*>(instance);
  if (inst == nullptr) return false;
  std::stack<const uhdm::Any*> stack;
  const uhdm::Any* tmp = expr;
  stack.push(tmp);
  while (!stack.empty()) {
    tmp = stack.top();
    stack.pop();
    uhdm::UhdmType type = tmp->getUhdmType();
    switch (type) {
      case uhdm::UhdmType::Range: {
        uhdm::Range* r = (uhdm::Range*)tmp;
        stack.push(r->getLeftExpr());
        stack.push(r->getRightExpr());
        break;
      }
      case uhdm::UhdmType::Constant: {
        if (const uhdm::RefTypespec* rt =
                ((uhdm::Constant*)tmp)->getTypespec()) {
          if (const uhdm::Any* tp = rt->getActual()) {
            stack.push(tp);
          }
        }
        break;
      }
      case uhdm::UhdmType::TypedefTypespec: {
        stack.push(tmp);
        break;
      }
      case uhdm::UhdmType::LogicTypespec: {
        uhdm::LogicTypespec* tps = (uhdm::LogicTypespec*)tmp;
        if (tps->getRanges()) {
          for (auto op : *tps->getRanges()) {
            stack.push(op);
          }
        }
        break;
      }
      case uhdm::UhdmType::BitTypespec: {
        uhdm::BitTypespec* tps = (uhdm::BitTypespec*)tmp;
        if (tps->getRanges()) {
          for (auto op : *tps->getRanges()) {
            stack.push(op);
          }
        }
        break;
      }
      case uhdm::UhdmType::ArrayTypespec: {
        uhdm::ArrayTypespec* tps = (uhdm::ArrayTypespec*)tmp;
        if (tps->getRanges()) {
          for (auto op : *tps->getRanges()) {
            stack.push(op);
          }
        }
        if (const uhdm::RefTypespec* rt = tps->getElemTypespec()) {
          if (const uhdm::Any* etps = rt->getActual()) {
            stack.push(etps);
          }
        }
        break;
      }
      case uhdm::UhdmType::PackedArrayTypespec: {
        uhdm::PackedArrayTypespec* tps = (uhdm::PackedArrayTypespec*)tmp;
        if (tps->getRanges()) {
          for (auto op : *tps->getRanges()) {
            stack.push(op);
          }
        }
        if (const uhdm::RefTypespec* rt = tps->getElemTypespec()) {
          if (const uhdm::Any* etps = rt->getActual()) {
            stack.push(etps);
          }
        }
        break;
      }
      case uhdm::UhdmType::Parameter:
      case uhdm::UhdmType::RefObj:
      case uhdm::UhdmType::TypeParameter: {
        if (inst->isOverridenParam(tmp->getName())) return true;
        break;
      }
      case uhdm::UhdmType::Operation: {
        uhdm::Operation* oper = (uhdm::Operation*)tmp;
        for (auto op : *oper->getOperands()) {
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
