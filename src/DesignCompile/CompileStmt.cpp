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
 * File:   CompileStmt.cpp
 * Author: alain
 *
 * Created on May 14, 2019, 8:03 PM
 */

#include "Surelog/Common/FileSystem.h"
#include "Surelog/Design/BindStmt.h"
#include "Surelog/Design/Design.h"
#include "Surelog/Design/Enum.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/Design/Function.h"
#include "Surelog/Design/ModuleDefinition.h"
#include "Surelog/Design/ModuleInstance.h"
#include "Surelog/Design/Netlist.h"
#include "Surelog/Design/Task.h"
#include "Surelog/DesignCompile/CompileDesign.h"
#include "Surelog/DesignCompile/CompileHelper.h"
#include "Surelog/DesignCompile/UhdmWriter.h"
#include "Surelog/ErrorReporting/ErrorContainer.h"
#include "Surelog/ErrorReporting/ErrorDefinition.h"
#include "Surelog/ErrorReporting/Location.h"
#include "Surelog/Expression/ExprBuilder.h"
#include "Surelog/Expression/Value.h"
#include "Surelog/Library/Library.h"
#include "Surelog/Package/Package.h"
#include "Surelog/SourceCompile/CompilationUnit.h"
#include "Surelog/SourceCompile/CompileSourceFile.h"
#include "Surelog/SourceCompile/Compiler.h"
#include "Surelog/SourceCompile/ParseFile.h"
#include "Surelog/SourceCompile/PreprocessFile.h"
#include "Surelog/SourceCompile/SymbolTable.h"
#include "Surelog/SourceCompile/VObjectTypes.h"
#include "Surelog/Testbench/ClassDefinition.h"
#include "Surelog/Testbench/Property.h"
#include "Surelog/Utils/StringUtils.h"

// UHDM
#include <uhdm/ElaboratorListener.h>
#include <uhdm/sv_vpi_user.h>
#include <uhdm/uhdm.h>
#include <uhdm/vpi_user.h>

#include <cstdint>
#include <functional>
#include <iostream>
#include <map>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace SURELOG {

using namespace UHDM;  // NOLINT (using a bunch of these)

any* CompileHelper::searchObjectName(std::string_view name,
                                     DesignComponent* component,
                                     CompileDesign* compileDesign, any* stmt) {
  any* object = nullptr;
  auto [func, actual_comp] =
      getTaskFunc(name, component, compileDesign, nullptr, stmt);
  if (func) {
    object = func;
  }
  if (object == nullptr) {
    if (stmt) {
      if (stmt->VpiName() == name) {
        object = stmt;
      }
      if (object == nullptr) {
        if (scope* sc = any_cast<UHDM::scope*>(stmt)) {
          if (sc->Scopes()) {
            for (scope* s : *sc->Scopes()) {
              if (s->VpiName() == name) {
                object = s;
                break;
              }
            }
          }
        }
      }
      if (object == nullptr) {
        if (stmt->VpiParent()) {
          if (any* tmp = searchObjectName(name, component, compileDesign,
                                          (any*)stmt->VpiParent())) {
            object = tmp;
          }
        }
      }
    }
  }
  return object;
}

VectorOfany* CompileHelper::compileStmt(DesignComponent* component,
                                        const FileContent* fC, NodeId the_stmt,
                                        CompileDesign* compileDesign,
                                        Reduce reduce, UHDM::any* pstmt,
                                        ValuedComponentI* instance,
                                        bool muteErrors) {
  FileSystem* const fileSystem = FileSystem::getInstance();
  VectorOfany* results = nullptr;
  UHDM::Serializer& s = compileDesign->getSerializer();
  VObjectType type = fC->Type(the_stmt);
  UHDM::VectorOfattribute* attributes = nullptr;
  if (type == VObjectType::paAttribute_instance) {
    attributes =
        compileAttributes(component, fC, the_stmt, compileDesign, nullptr);
    while (fC->Type(the_stmt) == VObjectType::paAttribute_instance)
      the_stmt = fC->Sibling(the_stmt);
  }
  type = fC->Type(the_stmt);
  UHDM::any* stmt = nullptr;
  switch (type) {
    case VObjectType::paModule_common_item:
    case VObjectType::paModule_or_generate_item:
    case VObjectType::paModule_or_generate_item_declaration:
    case VObjectType::paPackage_or_generate_item_declaration:
    case VObjectType::paGenerate_item: {
      if (instance) break;
      NodeId child = fC->Child(the_stmt);
      if (!child) {
        // That is the null statement (no statement)
        return nullptr;
      }
      results = compileStmt(component, fC, child, compileDesign, reduce, pstmt,
                            instance, muteErrors);
      break;
    }
    case VObjectType::paGenerate_region: {
      VectorOfgen_stmt* sts =
          compileGenStmt(valuedcomponenti_cast<ModuleDefinition*>(component),
                         fC, compileDesign, the_stmt);
      if (!sts->empty()) stmt = sts->front();
      break;
    }
    case VObjectType::paGenerate_begin_end_block: {
      if (instance) break;
      NodeId child = fC->Child(the_stmt);
      if (!child) {
        // That is the null statement (no statement)
        return nullptr;
      }
      if (fC->Sibling(child)) {
        results = s.MakeAnyVec();
        NodeId tmp = child;
        while (tmp) {
          if (fC->Type(tmp) != VObjectType::slStringConst) {
            VectorOfany* stmts =
                compileStmt(component, fC, tmp, compileDesign, reduce, pstmt,
                            instance, muteErrors);
            if (stmts) {
              for (any* st : *stmts) {
                results->push_back(st);
              }
            }
          }
          tmp = fC->Sibling(tmp);
        }
      } else {
        results = compileStmt(component, fC, child, compileDesign, reduce,
                              pstmt, instance, muteErrors);
      }
      break;
    }
    case VObjectType::paConditional_generate_construct: {
      NodeId child = fC->Child(the_stmt);
      if (!child) {
        // That is the null statement (no statement)
        return nullptr;
      }
      VectorOfgen_stmt* sts =
          compileGenStmt(valuedcomponenti_cast<ModuleDefinition*>(component),
                         fC, compileDesign, the_stmt);
      if (!sts->empty()) stmt = sts->front();
      break;
    }
    case VObjectType::paStatement_or_null: {
      NodeId child = fC->Child(the_stmt);
      if (!child) {
        // That is the null statement (no statement)
        return nullptr;
      }
      results = compileStmt(component, fC, child, compileDesign, reduce, pstmt,
                            instance, muteErrors);
      break;
    }
    case VObjectType::paBlock_item_declaration:
    case VObjectType::paTf_item_declaration:
    case VObjectType::paStatement:
    case VObjectType::paJump_statement:
    case VObjectType::paStatement_item:
    case VObjectType::paImmediate_assertion_statement:
    case VObjectType::paProcedural_assertion_statement:
    case VObjectType::paLoop_statement: {
      results = compileStmt(component, fC, fC->Child(the_stmt), compileDesign,
                            reduce, pstmt, instance, muteErrors);
      break;
    }
    case VObjectType::paInc_or_dec_expression: {
      stmt = compileExpression(component, fC, the_stmt, compileDesign,
                               Reduce::No, pstmt, instance);
      break;
    }
    case VObjectType::paProcedural_timing_control_statement: {
      UHDM::atomic_stmt* dc = compileProceduralTimingControlStmt(
          component, fC, fC->Child(the_stmt), compileDesign, pstmt, instance);
      stmt = dc;
      break;
    }
    case VObjectType::paNonblocking_assignment: {
      NodeId Operator_assignment = the_stmt;
      UHDM::assignment* assign =
          compileBlockingAssignment(component, fC, Operator_assignment, false,
                                    compileDesign, pstmt, instance);
      stmt = assign;
      break;
    }
    case VObjectType::paBlocking_assignment:
    case VObjectType::paOperator_assignment: {
      NodeId Operator_assignment = fC->Child(the_stmt);
      UHDM::assignment* assign =
          compileBlockingAssignment(component, fC, Operator_assignment, true,
                                    compileDesign, pstmt, instance);
      stmt = assign;
      break;
    }
    case VObjectType::paSubroutine_call_statement: {
      NodeId Subroutine_call = fC->Child(the_stmt);
      stmt =
          compileTfCall(component, fC, Subroutine_call, compileDesign, pstmt);
      break;
    }
    case VObjectType::paSystem_task: {
      stmt = compileTfCall(component, fC, the_stmt, compileDesign, pstmt);
      break;
    }
    case VObjectType::paConditional_statement: {
      NodeId Conditional_statement = the_stmt;
      NodeId Cond_predicate = fC->Child(Conditional_statement);
      UHDM::atomic_stmt* cstmt = compileConditionalStmt(
          component, fC, Cond_predicate, compileDesign, pstmt, instance);
      stmt = cstmt;
      break;
    }
    case VObjectType::paCond_predicate: {
      NodeId Cond_predicate = the_stmt;
      UHDM::atomic_stmt* cstmt = compileConditionalStmt(
          component, fC, Cond_predicate, compileDesign, pstmt, instance);
      stmt = cstmt;
      break;
    }
    case VObjectType::paRandcase_statement: {
      NodeId Case_statement = the_stmt;
      UHDM::atomic_stmt* cstmt = compileRandcaseStmt(
          component, fC, Case_statement, compileDesign, pstmt, instance);
      stmt = cstmt;
      break;
    }
    case VObjectType::paCase_statement: {
      NodeId Case_statement = the_stmt;
      UHDM::atomic_stmt* cstmt = compileCaseStmt(
          component, fC, Case_statement, compileDesign, pstmt, instance);
      stmt = cstmt;
      break;
    }
    case VObjectType::paSeq_block: {
      NodeId item = fC->Child(the_stmt);
      VectorOfany* stmts = s.MakeAnyVec();
      UHDM::scope* scope = nullptr;
      std::string label, endLabel;
      NodeId labelId, endLabelId;
      if (fC->Type(item) == VObjectType::slStringConst) {
        labelId = item;
        item = fC->Sibling(item);
      } else {
        NodeId Statement_item = fC->Parent(the_stmt);
        NodeId Statement = fC->Parent(Statement_item);
        NodeId Label = fC->Child(Statement);
        if (fC->Sibling(Label) == Statement_item) {
          if (fC->Type(Label) == VObjectType::slStringConst) labelId = Label;
        }
      }
      NodeId tempItem = item;
      while (tempItem) {
        if (fC->Type(tempItem) == VObjectType::paEND) {
          if ((endLabelId = fC->Sibling(tempItem))) {
            break;
          }
        }
        tempItem = fC->Sibling(tempItem);
      }
      if (labelId || endLabelId) {
        UHDM::named_begin* begin = s.MakeNamed_begin();
        begin->Stmts(stmts);
        if (labelId) {
          label = fC->SymName(labelId);
          begin->VpiName(label);
        }
        if (endLabelId) {
          endLabel = fC->SymName(endLabelId);
          begin->VpiEndLabel(endLabel);
        }
        stmt = begin;
        scope = begin;
      } else {
        UHDM::begin* begin = s.MakeBegin();
        labelId = the_stmt;
        begin->Stmts(stmts);
        stmt = begin;
        scope = begin;
      }
      scope->VpiParent(pstmt);
      fC->populateCoreMembers(labelId, labelId, scope);
      if (labelId && endLabelId && (label != endLabel)) {
        ErrorContainer* errors =
            compileDesign->getCompiler()->getErrorContainer();
        SymbolTable* symbols = compileDesign->getCompiler()->getSymbolTable();
        Location loc(fC->getFileId(), fC->Line(labelId), fC->Column(labelId),
                     symbols->registerSymbol(label));
        Location loc2(fC->getFileId(), fC->Line(endLabelId),
                      fC->Column(endLabelId),
                      symbols->registerSymbol(endLabel));
        Error err(ErrorDefinition::COMP_UNMATCHED_LABEL, loc, loc2);
        errors->addError(err);
      }
      while (item && (fC->Type(item) != VObjectType::paEND)) {
        if (VectorOfany* cstmts =
                compileStmt(component, fC, item, compileDesign, Reduce::No,
                            stmt, instance, muteErrors)) {
          for (any* cstmt : *cstmts) {
            bool isDecl = false;
            if (cstmt->UhdmType() == uhdmassignment) {
              assignment* assign = (assignment*)cstmt;
              if (assign->Rhs() == nullptr) {
                isDecl = true;
                if (assign->Lhs()) ((variables*)assign->Lhs())->VpiParent(stmt);
              }
            } else if (cstmt->UhdmType() == uhdmsequence_decl) {
              VectorOfsequence_decl* decls = scope->Sequence_decls();
              if (decls == nullptr) {
                decls = s.MakeSequence_declVec();
                scope->Sequence_decls(decls);
              }
              decls->push_back((sequence_decl*)cstmt);
              isDecl = true;
            }
            if (!isDecl) {
              stmts->push_back(cstmt);
              cstmt->VpiParent(stmt);
            }
          }
        }
        item = fC->Sibling(item);
      }
      break;
    }
    case VObjectType::paPar_block: {
      NodeId item = fC->Child(the_stmt);
      VectorOfany* stmts = s.MakeAnyVec();
      UHDM::scope* scope = nullptr;
      std::string label, endLabel;
      NodeId labelId, endLabelId;
      if (fC->Type(item) == VObjectType::slStringConst) {
        labelId = item;
        item = fC->Sibling(item);
      } else {
        NodeId Statement_item = fC->Parent(the_stmt);
        NodeId Statement = fC->Parent(Statement_item);
        NodeId Label = fC->Child(Statement);
        if (fC->Sibling(Label) == Statement_item) {
          if (fC->Type(Label) == VObjectType::slStringConst) labelId = Label;
        }
      }
      // Get join label if any
      NodeId tempItem = fC->Sibling(item);
      while (tempItem) {
        VObjectType type = fC->Type(tempItem);
        if ((type == VObjectType::paJoin_keyword) ||
            (type == VObjectType::paJoin_any_keyword) ||
            (type == VObjectType::paJoin_none_keyword)) {
          if ((endLabelId = fC->Sibling(tempItem))) {
            break;
          }
        }
        tempItem = fC->Sibling(tempItem);
      }
      if (labelId || endLabelId) {
        UHDM::named_fork* fork = s.MakeNamed_fork();
        fork->Stmts(stmts);
        if (labelId) {
          label = fC->SymName(labelId);
          fork->VpiName(label);
        }
        if (endLabelId) {
          endLabel = fC->SymName(endLabelId);
          fork->VpiEndLabel(endLabel);
        }
        stmt = fork;
        scope = fork;
      } else {
        labelId = the_stmt;
        UHDM::fork_stmt* fork = s.MakeFork_stmt();
        fork->Stmts(stmts);
        stmt = fork;
        scope = fork;
      }
      scope->VpiParent(pstmt);
      while (item) {
        if (VectorOfany* cstmts =
                compileStmt(component, fC, item, compileDesign, Reduce::No,
                            stmt, instance, muteErrors)) {
          for (any* cstmt : *cstmts) {
            bool isDecl = false;
            if (cstmt->UhdmType() == uhdmassignment) {
              assignment* assign = (assignment*)cstmt;
              if (assign->Rhs() == nullptr) {
                VectorOfvariables* vars = scope->Variables();
                if (vars == nullptr) {
                  isDecl = true;
                  vars = s.MakeVariablesVec();
                  scope->Variables(vars);
                }
                if (assign->Lhs()) {
                  vars->push_back((UHDM::variables*)assign->Lhs());
                  ((variables*)assign->Lhs())->VpiParent(stmt);
                }
              }
            }
            if (!isDecl) {
              stmts->push_back(cstmt);
              cstmt->VpiParent(stmt);
            }
          }
        }
        item = fC->Sibling(item);
        if (item) {
          VObjectType jointype = fC->Type(item);
          int32_t vpijointype = 0;
          if (jointype == VObjectType::paJoin_keyword ||
              jointype == VObjectType::paJoin_any_keyword ||
              jointype == VObjectType::paJoin_none_keyword) {
            if (NodeId endLabel = fC->Sibling(item)) {
              const std::string_view endlabel = fC->SymName(endLabel);
              if (endlabel != label) {
                ErrorContainer* errors =
                    compileDesign->getCompiler()->getErrorContainer();
                SymbolTable* symbols =
                    compileDesign->getCompiler()->getSymbolTable();
                Location loc(fC->getFileId(), fC->Line(labelId),
                             fC->Column(labelId),
                             symbols->registerSymbol(label));
                Location loc2(fC->getFileId(), fC->Line(endLabel),
                              fC->Column(endLabel),
                              symbols->registerSymbol(endlabel));
                Error err(ErrorDefinition::COMP_UNMATCHED_LABEL, loc, loc2);
                errors->addError(err);
              }
            }
          }

          if (jointype == VObjectType::paJoin_keyword) {
            vpijointype = vpiJoin;
            if (stmt->UhdmType() == uhdmnamed_fork) {
              ((UHDM::named_fork*)stmt)->VpiJoinType(vpijointype);
            } else {
              ((UHDM::fork_stmt*)stmt)->VpiJoinType(vpijointype);
            }
            break;
          } else if (jointype == VObjectType::paJoin_any_keyword) {
            vpijointype = vpiJoinAny;
            if (stmt->UhdmType() == uhdmnamed_fork) {
              ((UHDM::named_fork*)stmt)->VpiJoinType(vpijointype);
            } else {
              ((UHDM::fork_stmt*)stmt)->VpiJoinType(vpijointype);
            }
            break;
          } else if (jointype == VObjectType::paJoin_none_keyword) {
            vpijointype = vpiJoinNone;
            if (stmt->UhdmType() == uhdmnamed_fork) {
              ((UHDM::named_fork*)stmt)->VpiJoinType(vpijointype);
            } else {
              ((UHDM::fork_stmt*)stmt)->VpiJoinType(vpijointype);
            }
            break;
          }
        }
      }
      break;
    }
    case VObjectType::paFOREVER: {
      UHDM::forever_stmt* forever = s.MakeForever_stmt();
      NodeId item = fC->Sibling(the_stmt);
      if (VectorOfany* forev =
              compileStmt(component, fC, item, compileDesign, Reduce::No,
                          forever, instance, muteErrors)) {
        any* stmt = (*forev)[0];
        stmt->VpiParent(forever);
        forever->VpiStmt(stmt);
      }
      stmt = forever;
      break;
    }
    case VObjectType::paFOREACH: {
      UHDM::foreach_stmt* for_each = s.MakeForeach_stmt();
      NodeId Ps_or_hierarchical_array_identifier = fC->Sibling(the_stmt);
      UHDM::any* var = compileVariable(
          component, fC, fC->Child(Ps_or_hierarchical_array_identifier),
          compileDesign, Reduce::No, for_each, nullptr, false);
      NodeId Loop_variables = fC->Sibling(Ps_or_hierarchical_array_identifier);
      NodeId loopVarId = fC->Child(Loop_variables);
      NodeId Statement = Loop_variables;
      VectorOfany* loop_vars = s.MakeAnyVec();
      while (fC->Type(Statement) == VObjectType::slStringConst ||
             fC->Type(Statement) == VObjectType::paLoop_variables ||
             fC->Type(Statement) == VObjectType::paComma) {
        if (fC->Type(Statement) == VObjectType::slStringConst) {
          loopVarId = Statement;
        } else if (fC->Type(Statement) == VObjectType::paComma) {
          operation* op = s.MakeOperation();
          fC->populateCoreMembers(Statement, Statement, op);
          op->VpiOpType(vpiNullOp);
          loop_vars->push_back(op);
        } else {
          loopVarId = fC->Child(Statement);
        }
        while (loopVarId) {
          ref_var* ref = s.MakeRef_var();
          ref->VpiName(fC->SymName(loopVarId));
          fC->populateCoreMembers(loopVarId, loopVarId, ref);
          typespec* tps = s.MakeUnsupported_typespec();
          tps->VpiName(fC->SymName(loopVarId));
          fC->populateCoreMembers(loopVarId, loopVarId, tps);
          tps->VpiParent(ref);
          if (ref->Typespec() == nullptr) {
            ref_typespec* tpsRef = s.MakeRef_typespec();
            tpsRef->VpiParent(ref);
            ref->Typespec(tpsRef);
          }
          ref->Typespec()->Actual_typespec(tps);
          component->needLateTypedefBinding(ref);
          loop_vars->push_back(ref);
          ref->VpiParent(for_each);
          loopVarId = fC->Sibling(loopVarId);
          while (fC->Type(loopVarId) == VObjectType::paComma) {
            NodeId lookahead = fC->Sibling(loopVarId);
            if (fC->Type(lookahead) == VObjectType::paComma) {
              operation* op = s.MakeOperation();
              fC->populateCoreMembers(loopVarId, loopVarId, op);
              op->VpiOpType(vpiNullOp);
              loop_vars->push_back(op);
              loopVarId = fC->Sibling(loopVarId);
              continue;
            } else {
              break;
            }
          }
          if ((fC->Type(loopVarId) != VObjectType::slStringConst) &&
              ((fC->Type(loopVarId) != VObjectType::paComma))) {
            break;
          }
          if (fC->Type(loopVarId) == VObjectType::paComma) {
            loopVarId = fC->Sibling(loopVarId);
          }
        }
        Statement = fC->Sibling(Statement);
      }
      for_each->VpiLoopVars(loop_vars);
      if (VectorOfany* forev =
              compileStmt(component, fC, Statement, compileDesign, Reduce::No,
                          for_each, instance, muteErrors)) {
        any* stmt = (*forev)[0];
        stmt->VpiParent(for_each);
        for_each->VpiStmt(stmt);
      }
      if (var) {
        var->VpiParent(for_each);
        for_each->Variable((variables*)var);
      }
      stmt = for_each;
      break;
    }
    case VObjectType::paProcedural_continuous_assignment: {
      any* conta = compileProceduralContinuousAssign(component, fC, the_stmt,
                                                     compileDesign);
      stmt = conta;
      break;
    }
    case VObjectType::paParameter_declaration:
    case VObjectType::paLocal_parameter_declaration: {
      NodeId Data_type_or_implicit = fC->Child(the_stmt);
      UHDM::typespec* ts =
          compileTypespec(component, fC, fC->Child(Data_type_or_implicit),
                          compileDesign, Reduce::Yes, nullptr, nullptr, false);
      NodeId List_of_param_assignments = fC->Sibling(Data_type_or_implicit);
      NodeId Param_assignment = fC->Child(List_of_param_assignments);
      UHDM::VectorOfany* param_assigns = s.MakeAnyVec();
      while (Param_assignment) {
        NodeId name = fC->Child(Param_assignment);
        NodeId value = fC->Sibling(name);
        UHDM::parameter* param = s.MakeParameter();
        fC->populateCoreMembers(Param_assignment, Param_assignment, param);
        // Unpacked dimensions
        if (fC->Type(value) == VObjectType::paUnpacked_dimension) {
          int32_t unpackedSize;
          std::vector<UHDM::range*>* unpackedDimensions =
              compileRanges(component, fC, value, compileDesign, Reduce::Yes,
                            param, nullptr, unpackedSize, false);
          param->Ranges(unpackedDimensions);
          param->VpiSize(unpackedSize);
          while (fC->Type(value) == VObjectType::paUnpacked_dimension) {
            value = fC->Sibling(value);
          }
        }
        param->VpiLocalParam(true);
        UHDM::param_assign* param_assign = s.MakeParam_assign();
        fC->populateCoreMembers(Param_assignment, Param_assignment,
                                param_assign);
        param_assigns->push_back(param_assign);
        param->VpiParent(param_assign);
        param->VpiName(fC->SymName(name));
        if (ts != nullptr) {
          if (param->Typespec() == nullptr) {
            ref_typespec* tsRef = s.MakeRef_typespec();
            tsRef->VpiParent(param);
            param->Typespec(tsRef);
          }
          param->Typespec()->Actual_typespec(ts);
        }
        param_assign->Lhs(param);
        param_assign->Rhs((expr*)compileExpression(
            component, fC, value, compileDesign,
            ((reduce == Reduce::Yes) || instance) ? Reduce::Yes : Reduce::No,
            param_assign, nullptr));
        Param_assignment = fC->Sibling(Param_assignment);
      }
      results = param_assigns;
      break;
    }
    case VObjectType::paREPEAT: {
      NodeId cond = fC->Sibling(the_stmt);
      NodeId rstmt = fC->Sibling(cond);
      UHDM::repeat* repeat = s.MakeRepeat();
      if (UHDM::any* cond_exp = compileExpression(
              component, fC, cond, compileDesign, Reduce::No, repeat)) {
        repeat->VpiCondition((UHDM::expr*)cond_exp);
      }
      if (VectorOfany* repeat_stmts =
              compileStmt(component, fC, rstmt, compileDesign, Reduce::No,
                          repeat, instance, muteErrors)) {
        any* stmt = (*repeat_stmts)[0];
        repeat->VpiStmt(stmt);
        stmt->VpiParent(repeat);
      }
      stmt = repeat;
      break;
    }
    case VObjectType::paWHILE: {
      NodeId cond = fC->Sibling(the_stmt);
      NodeId rstmt = fC->Sibling(cond);
      UHDM::while_stmt* while_st = s.MakeWhile_stmt();
      if (UHDM::any* cond_exp = compileExpression(
              component, fC, cond, compileDesign, Reduce::No, while_st)) {
        while_st->VpiCondition((UHDM::expr*)cond_exp);
      }
      if (VectorOfany* while_stmts =
              compileStmt(component, fC, rstmt, compileDesign, Reduce::No,
                          while_st, instance, muteErrors)) {
        any* stmt = (*while_stmts)[0];
        while_st->VpiStmt(stmt);
        stmt->VpiParent(while_st);
      }
      stmt = while_st;
      break;
    }
    case VObjectType::paDO: {
      NodeId Statement_or_null = fC->Sibling(the_stmt);
      NodeId Condition = fC->Sibling(Statement_or_null);
      UHDM::do_while* do_while = s.MakeDo_while();
      if (NodeId Statement = fC->Child(Statement_or_null)) {
        VectorOfany* while_stmts =
            compileStmt(component, fC, Statement, compileDesign, Reduce::No,
                        do_while, instance, muteErrors);
        if (while_stmts && !while_stmts->empty()) {
          any* stmt = (*while_stmts)[0];
          do_while->VpiStmt(stmt);
          stmt->VpiParent(do_while);
        }
      }
      if (UHDM::any* cond_exp = compileExpression(
              component, fC, Condition, compileDesign, Reduce::No, do_while)) {
        do_while->VpiCondition((UHDM::expr*)cond_exp);
      }
      fC->populateCoreMembers(the_stmt, Condition, do_while);
      stmt = do_while;
      break;
    }
    case VObjectType::paWait_statement: {
      NodeId Expression = fC->Child(the_stmt);
      if (!Expression) {
        // wait fork
        UHDM::wait_fork* waitst = s.MakeWait_fork();
        stmt = waitst;
      } else if (fC->Type(Expression) == VObjectType::paExpression) {
        // wait
        NodeId Statement_or_null = fC->Sibling(Expression);
        UHDM::wait_stmt* waitst = s.MakeWait_stmt();
        if (NodeId Statement = fC->Child(Statement_or_null)) {
          VectorOfany* while_stmts =
              compileStmt(component, fC, Statement, compileDesign, Reduce::No,
                          waitst, instance, muteErrors);
          if (while_stmts && !while_stmts->empty()) {
            any* stmt = (*while_stmts)[0];
            waitst->VpiStmt(stmt);
            stmt->VpiParent(waitst);
          }
        }
        if (UHDM::any* cond_exp = compileExpression(
                component, fC, Expression, compileDesign, Reduce::No, waitst)) {
          waitst->VpiCondition((UHDM::expr*)cond_exp);
        }
        stmt = waitst;
      } else {
        // wait order
        UHDM::ordered_wait* waitst = s.MakeOrdered_wait();
        stmt = waitst;
        VectorOfany* conditions = s.MakeAnyVec();
        waitst->VpiConditions(conditions);
        NodeId Hierarchical_identifier = Expression;
        while (Hierarchical_identifier &&
               (fC->Type(Hierarchical_identifier) ==
                VObjectType::paHierarchical_identifier)) {
          if (UHDM::any* cond_exp =
                  compileExpression(component, fC, Hierarchical_identifier,
                                    compileDesign, Reduce::No, waitst)) {
            conditions->push_back(cond_exp);
          }
          Hierarchical_identifier = fC->Sibling(Hierarchical_identifier);
        }
        NodeId Action_block = Hierarchical_identifier;
        NodeId Stmt = fC->Child(Action_block);
        if (fC->Type(Stmt) == VObjectType::paStatement_or_null) {
          // If only
          if (VectorOfany* if_stmts =
                  compileStmt(component, fC, Stmt, compileDesign, Reduce::No,
                              waitst, instance, muteErrors)) {
            if (!if_stmts->empty()) {
              any* stmt = (*if_stmts)[0];
              waitst->VpiStmt(stmt);
              stmt->VpiParent(waitst);
            }
          }
        } else if (fC->Type(Stmt) == VObjectType::paELSE) {
          // Else Only
          Stmt = fC->Sibling(Stmt);
          if (VectorOfany* if_stmts =
                  compileStmt(component, fC, Stmt, compileDesign, Reduce::No,
                              waitst, instance, muteErrors)) {
            if (!if_stmts->empty()) {
              any* stmt = (*if_stmts)[0];
              waitst->VpiElseStmt(stmt);
              stmt->VpiParent(waitst);
            }
          }
        } else {
          // if else
          if (VectorOfany* if_stmts =
                  compileStmt(component, fC, Stmt, compileDesign, Reduce::No,
                              waitst, instance, muteErrors)) {
            if (!if_stmts->empty()) {
              any* stmt = (*if_stmts)[0];
              waitst->VpiStmt(stmt);
              stmt->VpiParent(waitst);
            }
          }
          NodeId Else = fC->Sibling(Stmt);
          Stmt = fC->Sibling(Else);
          if (VectorOfany* else_stmts =
                  compileStmt(component, fC, Stmt, compileDesign, Reduce::No,
                              waitst, instance, muteErrors)) {
            if (!else_stmts->empty()) {
              any* stmt = (*else_stmts)[0];
              waitst->VpiElseStmt(stmt);
              stmt->VpiParent(waitst);
            }
          }
        }
      }
      break;
    }
    case VObjectType::paEvent_trigger: {
      UHDM::event_stmt* estmt = s.MakeEvent_stmt();
      NodeId Trigger_type = fC->Child(the_stmt);
      if (fC->Type(Trigger_type) != VObjectType::paNonBlockingTriggerEvent) {
        estmt->VpiBlocking(true);
      }
      stmt = estmt;
      NodeId Hierarchical_identifier = fC->Sibling(Trigger_type);
      if (expr* exp =
              (expr*)compileExpression(component, fC, Hierarchical_identifier,
                                       compileDesign, Reduce::No, estmt)) {
        estmt->VpiName(exp->VpiName());
      }
      break;
    }
    case VObjectType::paFOR: {
      UHDM::any* loop =
          compileForLoop(component, fC, the_stmt, compileDesign, pstmt);
      stmt = loop;
      break;
    }
    case VObjectType::paRETURN: {
      UHDM::return_stmt* return_stmt = s.MakeReturn_stmt();
      if (NodeId cond = fC->Sibling(the_stmt)) {
        if (expr* exp =
                (expr*)compileExpression(component, fC, cond, compileDesign,
                                         reduce, return_stmt, instance, true)) {
          return_stmt->VpiCondition(exp);
        }
      }
      stmt = return_stmt;
      break;
    }
    case VObjectType::paBREAK: {
      UHDM::break_stmt* bstmt = s.MakeBreak_stmt();
      stmt = bstmt;
      break;
    }
    case VObjectType::paDisable_statement: {
      NodeId exp = fC->Child(the_stmt);
      if (exp) {
        UHDM::disable* disable = s.MakeDisable();
        if (expr* expc = (expr*)compileExpression(
                component, fC, exp, compileDesign, Reduce::No, disable)) {
          if (expc->UhdmType() == uhdmref_obj) {
            const std::string_view name = expc->VpiName();
            if (any* object =
                    searchObjectName(name, component, compileDesign, pstmt)) {
              disable->VpiExpr(object);
            }
          }
        }
        stmt = disable;
      } else {
        UHDM::disable_fork* disable = s.MakeDisable_fork();
        stmt = disable;
      }
      break;
    }
    case VObjectType::paCONTINUE: {
      UHDM::continue_stmt* cstmt = s.MakeContinue_stmt();
      stmt = cstmt;
      break;
    }
    case VObjectType::paRandsequence_statement: {
      sequence_decl* seqdecl = s.MakeSequence_decl();
      if (NodeId Name = fC->Child(the_stmt)) {
        const std::string_view name = fC->SymName(Name);
        seqdecl->VpiName(name);
      }
      stmt = seqdecl;
      break;
    }
    case VObjectType::paChecker_instantiation: {
      stmt = compileCheckerInstantiation(component, fC, fC->Child(the_stmt),
                                         compileDesign, pstmt, nullptr);
      break;
    }
    case VObjectType::paSimple_immediate_assertion_statement: {
      stmt = compileSimpleImmediateAssertion(component, fC, fC->Child(the_stmt),
                                             compileDesign, pstmt, nullptr);
      break;
    }
    case VObjectType::paDeferred_immediate_assertion_statement: {
      stmt = compileDeferredImmediateAssertion(
          component, fC, fC->Child(the_stmt), compileDesign, pstmt, nullptr);
      break;
    }
    case VObjectType::paProperty_declaration: {
      stmt = compilePropertyDeclaration(component, fC, fC->Child(the_stmt),
                                        compileDesign, pstmt, nullptr);
      break;
    }
    case VObjectType::paConcurrent_assertion_statement: {
      stmt = compileConcurrentAssertion(component, fC, fC->Child(the_stmt),
                                        compileDesign, pstmt, nullptr);
      break;
    }
    case VObjectType::paData_declaration: {
      results = compileDataDeclaration(component, fC, fC->Child(the_stmt),
                                       compileDesign, reduce, pstmt, instance);
      break;
    }
    case VObjectType::slStringConst: {
      if (VectorOfany* stmts =
              compileStmt(component, fC, fC->Sibling(the_stmt), compileDesign,
                          Reduce::No, pstmt, instance, muteErrors)) {
        const std::string_view label = fC->SymName(the_stmt);
        for (any* st : *stmts) {
          if (UHDM::atomic_stmt* stm = any_cast<atomic_stmt*>(st)) {
            stm->VpiName(label);
            fC->populateCoreMembers(the_stmt, InvalidNodeId, stm);
          } else if (UHDM::concurrent_assertions* stm =
                         any_cast<concurrent_assertions*>(st)) {
            stm->VpiName(label);
            fC->populateCoreMembers(the_stmt, InvalidNodeId, stm);
          }
        }
        results = stmts;
      }
      break;
    }
    case VObjectType::paExpect_property_statement: {
      expect_stmt* expect = s.MakeExpect_stmt();
      NodeId Property_expr = fC->Child(the_stmt);
      NodeId If_block = fC->Sibling(Property_expr);
      UHDM::any* if_stmt = nullptr;
      UHDM::any* else_stmt = nullptr;
      if (fC->Type(If_block) == VObjectType::paAction_block) {
        NodeId if_stmt_id = fC->Child(If_block);
        NodeId else_stmt_id;
        if (fC->Type(if_stmt_id) == VObjectType::paELSE) {
          else_stmt_id = fC->Sibling(if_stmt_id);
          if_stmt_id = InvalidNodeId;
        } else {
          NodeId else_keyword = fC->Sibling(if_stmt_id);
          if (else_keyword) else_stmt_id = fC->Sibling(else_keyword);
        }
        if (if_stmt_id) {
          if (UHDM::VectorOfany* if_stmts =
                  compileStmt(component, fC, if_stmt_id, compileDesign,
                              Reduce::No, expect, instance, muteErrors)) {
            if_stmt = (*if_stmts)[0];
          }
        }
        if (else_stmt_id) {
          if (UHDM::VectorOfany* else_stmts =
                  compileStmt(component, fC, else_stmt_id, compileDesign,
                              Reduce::No, expect, instance, muteErrors)) {
            else_stmt = (*else_stmts)[0];
          }
        }
      }
      UHDM::property_spec* prop_spec = s.MakeProperty_spec();
      NodeId Clocking_event = fC->Child(Property_expr);

      UHDM::expr* clocking_event = nullptr;
      if (fC->Type(Clocking_event) == VObjectType::paClocking_event) {
        clocking_event = (UHDM::expr*)compileExpression(
            component, fC, Clocking_event, compileDesign, Reduce::No, prop_spec,
            instance);
        Clocking_event = fC->Sibling(Clocking_event);
      }
      prop_spec->VpiClockingEvent(clocking_event);
      if (UHDM::expr* property_expr = any_cast<expr*>(
              compileExpression(component, fC, Clocking_event, compileDesign,
                                Reduce::No, prop_spec, instance))) {
        prop_spec->VpiPropertyExpr(property_expr);
      }
      fC->populateCoreMembers(Property_expr, Property_expr, prop_spec);
      prop_spec->VpiParent(expect);
      expect->Property_spec(prop_spec);
      expect->Stmt(if_stmt);
      expect->Else_stmt(else_stmt);
      stmt = expect;
      break;
    }
    case VObjectType::paContinuous_assign: {
      // Non-elab model
      component->lateBinding(false);
      VectorOfany* stmts = s.MakeAnyVec();
      auto assigns = compileContinuousAssignment(
          component, fC, fC->Child(the_stmt), compileDesign, nullptr);
      for (auto assign : assigns) {
        assign->VpiParent(pstmt);
        stmts->push_back(assign);
      }
      results = stmts;
      component->lateBinding(true);
      break;
    }
    case VObjectType::paInterface_instantiation:
    case VObjectType::paModule_instantiation:
    case VObjectType::paProgram_instantiation: {
      // Non-elab model
      ModuleDefinition* mod =
          valuedcomponenti_cast<ModuleDefinition*>(component);
      mod->lateBinding(false);
      std::pair<std::vector<UHDM::module_array*>,
                std::vector<UHDM::ref_module*>>
          result =
              compileInstantiation(mod, fC, compileDesign, the_stmt, nullptr);
      if (!result.first.empty()) {
        VectorOfany* stmts = s.MakeAnyVec();
        for (auto mod : result.first) {
          mod->VpiParent(pstmt);
          stmts->push_back(mod);
        }
        results = stmts;
      }
      if (!result.second.empty()) {
        VectorOfany* stmts = s.MakeAnyVec();
        for (auto mod : result.second) {
          mod->VpiParent(pstmt);
          stmts->push_back(mod);
        }
        results = stmts;
      }
      mod->lateBinding(true);
      break;
    }
    case VObjectType::paAlways_construct: {
      // Non-elab model
      ModuleDefinition* mod =
          valuedcomponenti_cast<ModuleDefinition*>(component);
      mod->lateBinding(false);
      UHDM::always* always =
          compileAlwaysBlock(mod, fC, the_stmt, compileDesign, nullptr);
      stmt = always;
      mod->lateBinding(true);
      break;
    }
    case VObjectType::paInitial_construct: {
      // Non-elab model
      ModuleDefinition* mod =
          valuedcomponenti_cast<ModuleDefinition*>(component);
      mod->lateBinding(false);
      UHDM::initial* init =
          compileInitialBlock(mod, fC, the_stmt, compileDesign);
      stmt = init;
      mod->lateBinding(true);
      break;
    }
    case VObjectType::paFinal_construct: {
      // Non-elab model
      ModuleDefinition* mod =
          valuedcomponenti_cast<ModuleDefinition*>(component);
      mod->lateBinding(false);
      UHDM::final_stmt* final =
          compileFinalBlock(mod, fC, the_stmt, compileDesign);
      stmt = final;
      mod->lateBinding(true);
      break;
    }
    default:
      break;
  }
  if (stmt) {
    if (attributes) {
      // Only attach attributes to following stmt
      if (UHDM::atomic_stmt* stm = any_cast<atomic_stmt*>(stmt)) {
        if (attributes) {
          stm->Attributes(attributes);
          for (auto a : *attributes) a->VpiParent(stm);
        }
      }
    }

    if (stmt->VpiLineNo() == 0) {
      fC->populateCoreMembers(the_stmt, the_stmt, stmt);
    }
    stmt->VpiParent(pstmt);
    results = s.MakeAnyVec();
    results->push_back(stmt);
  } else if (results) {
    for (any* st : *results) {
      st->VpiParent(pstmt);
      if (UHDM::atomic_stmt* stm = any_cast<atomic_stmt*>(st)) {
        if (attributes) {
          stm->Attributes(attributes);
          for (auto a : *attributes) a->VpiParent(stm);
        }
      }
    }
  } else {
    VObjectType stmttype = fC->Type(the_stmt);
    if ((muteErrors == false) && (stmttype != VObjectType::paEND) &&
        (stmttype != VObjectType::paJoin_keyword) &&
        (stmttype != VObjectType::paJoin_any_keyword) &&
        (stmttype != VObjectType::paJoin_none_keyword)) {
      ErrorContainer* errors =
          compileDesign->getCompiler()->getErrorContainer();
      SymbolTable* symbols = compileDesign->getCompiler()->getSymbolTable();
      unsupported_stmt* ustmt = s.MakeUnsupported_stmt();
      std::string lineText;
      fileSystem->readLine(fC->getFileId(), fC->Line(the_stmt), lineText);
      Location loc(fC->getFileId(the_stmt), fC->Line(the_stmt),
                   fC->Column(the_stmt),
                   symbols->registerSymbol(
                       StrCat("<", fC->printObject(the_stmt), "> ", lineText)));
      Error err(ErrorDefinition::UHDM_UNSUPPORTED_STMT, loc);
      errors->addError(err);
      ustmt->VpiValue(StrCat("STRING:", lineText));
      fC->populateCoreMembers(the_stmt, the_stmt, ustmt);
      ustmt->VpiParent(pstmt);
      stmt = ustmt;  // NOLINT
      // std::cout << "UNSUPPORTED STATEMENT: " << fC->getFileName(the_stmt)
      // << ":" << fC->Line(the_stmt) << ":" << std::endl; std::cout << " -> "
      // << fC->printObject(the_stmt) << std::endl;
    }
  }
  return results;
}

VectorOfany* CompileHelper::compileDataDeclaration(
    DesignComponent* component, const FileContent* fC, NodeId nodeId,
    CompileDesign* compileDesign, Reduce reduce, UHDM::any* pstmt,
    ValuedComponentI* instance) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  VectorOfany* results = nullptr;
  VObjectType type = fC->Type(nodeId);
  bool automatic_status = false;
  bool const_status = false;
  if (type == VObjectType::paLifetime_Automatic) {
    nodeId = fC->Sibling(nodeId);
    automatic_status = true;
    type = fC->Type(nodeId);
  }
  if (type == VObjectType::paLifetime_Static) {
    nodeId = fC->Sibling(nodeId);
    automatic_status = false;
    type = fC->Type(nodeId);
  }
  if (type == VObjectType::paConst_type) {
    nodeId = fC->Sibling(nodeId);
    const_status = true;
    type = fC->Type(nodeId);
  }
  switch (type) {
    case VObjectType::paAssertion_variable_declaration:
    case VObjectType::paVariable_declaration: {
      NodeId Data_type = fC->Child(nodeId);
      // typespec* ts = compileTypespec(component, fC, Data_type,
      // compileDesign);
      NodeId List_of_variable_decl_assignments = fC->Sibling(Data_type);
      if (fC->Type(List_of_variable_decl_assignments) ==
          VObjectType::paPacked_dimension) {
        List_of_variable_decl_assignments =
            fC->Sibling(List_of_variable_decl_assignments);
      }
      NodeId Variable_decl_assignment =
          fC->Child(List_of_variable_decl_assignments);
      VectorOfvariables* scovars = nullptr;
      if (scope* sco = any_cast<scope*>(pstmt)) {
        scovars = sco->Variables();
        if (scovars == nullptr) {
          scovars = s.MakeVariablesVec();
          sco->Variables(scovars);
        }
      }
      while (Variable_decl_assignment) {
        NodeId Var = Variable_decl_assignment;
        if (fC->Child(Var)) Var = fC->Child(Var);
        NodeId tmp = fC->Sibling(Var);
        std::vector<UHDM::range*>* unpackedDimensions = nullptr;
        if (fC->Type(tmp) != VObjectType::paExpression) {
          int32_t unpackedSize;
          unpackedDimensions =
              compileRanges(component, fC, tmp, compileDesign, reduce, nullptr,
                            instance, unpackedSize, false);
        }
        while (tmp && (fC->Type(tmp) != VObjectType::paExpression)) {
          tmp = fC->Sibling(tmp);
        }
        NodeId Expression = tmp;

        variables* var =
            (variables*)compileVariable(component, fC, Data_type, compileDesign,
                                        Reduce::No, pstmt, instance, false);

        if (var) {
          fC->populateCoreMembers(Var, Var, var);
          var->VpiConstantVariable(const_status);
          var->VpiAutomatic(automatic_status);
          var->VpiName(fC->SymName(Var));
          if (scovars) scovars->push_back(var);

          if (unpackedDimensions) {
            array_var* arr = s.MakeArray_var();
            fC->populateCoreMembers(Var, Var, arr);
            array_typespec* tps = s.MakeArray_typespec();
            if (ref_typespec* var_ts = var->Typespec()) {
              if (typespec* ts = var_ts->Actual_typespec()) {
                if (tps->Elem_typespec() == nullptr) {
                  ref_typespec* varRef = s.MakeRef_typespec();
                  varRef->VpiParent(tps);
                  tps->Elem_typespec(varRef);
                }
                tps->Elem_typespec()->Actual_typespec(ts);
              }
            }
            fC->populateCoreMembers(Var, fC->Sibling(Var), tps);
            tps->VpiEndLineNo(unpackedDimensions->back()->VpiEndLineNo());
            tps->VpiEndColumnNo(unpackedDimensions->back()->VpiEndColumnNo());
            tps->Ranges(unpackedDimensions);
            for (auto r : *unpackedDimensions) r->VpiParent(tps);
            if (arr->Typespec() == nullptr) {
              ref_typespec* tpsRef = s.MakeRef_typespec();
              tpsRef->VpiParent(arr);
              arr->Typespec(tpsRef);
            }
            arr->Typespec()->Actual_typespec(tps);
            for (range* r : *unpackedDimensions) {
              const expr* rrange = r->Right_expr();
              if (rrange->VpiValue() == "STRING:associative") {
                arr->VpiArrayType(vpiAssocArray);
                if (const ref_typespec* rrange_ts = rrange->Typespec()) {
                  if (const typespec* ts = rrange_ts->Actual_typespec()) {
                    if (tps->Index_typespec() == nullptr) {
                      ref_typespec* indexRef = s.MakeRef_typespec();
                      indexRef->VpiParent(tps);
                      tps->Index_typespec(indexRef);
                    }
                    tps->Index_typespec()->Actual_typespec(
                        const_cast<typespec*>(ts));
                  }
                }
              } else if (rrange->VpiValue() == "STRING:unsized") {
                arr->VpiArrayType(vpiDynamicArray);
              } else if (rrange->VpiValue() == "STRING:$") {
                arr->VpiArrayType(vpiQueueArray);
              } else {
                arr->VpiArrayType(vpiStaticArray);
              }
            }
            arr->VpiName(fC->SymName(Var));
            var->VpiName("");
            var->VpiParent(arr);
            if (scovars) scovars->push_back(arr);
            VectorOfvariables* vars = s.MakeVariablesVec();
            arr->Variables(vars);
            vars->push_back(var);
            var = arr;
          }
        }

        if (results == nullptr) {
          results = s.MakeAnyVec();
        }
        assignment* assign_stmt = s.MakeAssignment();
        assign_stmt->VpiOpType(vpiAssignmentOp);
        assign_stmt->VpiBlocking(true);
        if (var) {
          var->VpiParent(assign_stmt);
          assign_stmt->Lhs(var);
        }
        fC->populateCoreMembers(Variable_decl_assignment,
                                Variable_decl_assignment, assign_stmt);
        results->push_back(assign_stmt);
        if (Expression) {
          if (expr* rhs = (expr*)compileExpression(component, fC, Expression,
                                                   compileDesign, Reduce::No,
                                                   assign_stmt, instance)) {
            assign_stmt->Rhs(rhs);
          }
        }

        Variable_decl_assignment = fC->Sibling(Variable_decl_assignment);
      }
      break;
    }
    case VObjectType::paType_declaration: {
      if (pstmt) {
        // Keep type declaration local to the current stmt
        component = nullptr;
      }
      /* const DataType* dt = */ compileTypeDef(
          component, fC, fC->Parent(nodeId), compileDesign, Reduce::No, pstmt);
      if (results == nullptr) {
        results = s.MakeAnyVec();
        // Return an empty list of statements.
        // Type declaration are not executable statements.
      }
      break;
    }
    default:
      break;
  }
  return results;
}

UHDM::atomic_stmt* CompileHelper::compileConditionalStmt(
    DesignComponent* component, const FileContent* fC, NodeId Cond_predicate,
    CompileDesign* compileDesign, UHDM::any* pstmt, ValuedComponentI* instance,
    bool muteErrors) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  int32_t qualifier = 0;
  if (fC->Type(Cond_predicate) == VObjectType::paUnique_priority) {
    NodeId Qualifier = fC->Child(Cond_predicate);
    if (fC->Type(Qualifier) == VObjectType::paUNIQUE) {
      qualifier = vpiUniqueQualifier;
    } else if (fC->Type(Qualifier) == VObjectType::paPRIORITY) {
      qualifier = vpiPriorityQualifier;
    } else if (fC->Type(Qualifier) == VObjectType::paUNIQUE0) {
      qualifier = vpiUniqueQualifier;
    }
    Cond_predicate = fC->Sibling(Cond_predicate);
  }
  UHDM::any* cond_exp =
      compileExpression(component, fC, Cond_predicate, compileDesign,
                        Reduce::No, pstmt, instance);
  NodeId If_branch_stmt = fC->Sibling(Cond_predicate);
  NodeId Else_branch_stmt = fC->Sibling(If_branch_stmt);
  UHDM::atomic_stmt* result_stmt = nullptr;
  if (Else_branch_stmt) {
    UHDM::if_else* cond_stmt = s.MakeIf_else();
    cond_stmt->VpiQualifier(qualifier);
    cond_stmt->VpiCondition((UHDM::expr*)cond_exp);
    if (cond_exp && (cond_exp->VpiParent() == nullptr))
      cond_exp->VpiParent(cond_stmt);
    if (VectorOfany* if_stmts =
            compileStmt(component, fC, If_branch_stmt, compileDesign,
                        Reduce::No, cond_stmt, instance, muteErrors)) {
      cond_stmt->VpiStmt((*if_stmts)[0]);
    }
    if (VectorOfany* else_stmts =
            compileStmt(component, fC, Else_branch_stmt, compileDesign,
                        Reduce::No, cond_stmt, instance, muteErrors)) {
      cond_stmt->VpiElseStmt((*else_stmts)[0]);
    }
    result_stmt = cond_stmt;
  } else {
    UHDM::if_stmt* cond_stmt = s.MakeIf_stmt();
    cond_stmt->VpiQualifier(qualifier);
    cond_stmt->VpiCondition((UHDM::expr*)cond_exp);
    if (cond_exp && (cond_exp->VpiParent() == nullptr))
      cond_exp->VpiParent(cond_stmt);
    if (VectorOfany* if_stmts =
            compileStmt(component, fC, If_branch_stmt, compileDesign,
                        Reduce::No, cond_stmt, instance, muteErrors)) {
      cond_stmt->VpiStmt((*if_stmts)[0]);
    }
    result_stmt = cond_stmt;
  }
  return result_stmt;
}

UHDM::atomic_stmt* CompileHelper::compileEventControlStmt(
    DesignComponent* component, const FileContent* fC,
    NodeId Procedural_timing_control, CompileDesign* compileDesign,
    UHDM::any* pstmt, ValuedComponentI* instance, bool muteErrors) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  /*
  n<#100> u<70> t<IntConst> p<71> l<7>
  n<> u<71> t<Delay_control> p<72> c<70> l<7>
  n<> u<72> t<Procedural_timing_control> p<88> c<71> s<87> l<7>
  */
  NodeId Event_control = fC->Child(Procedural_timing_control);

  NodeId Event_expression = fC->Child(Event_control);
  UHDM::event_control* event = s.MakeEvent_control();
  fC->populateCoreMembers(Event_control, Event_control, event);
  event->VpiParent(pstmt);

  if (Event_expression) {
    if (UHDM::any* exp = compileExpression(component, fC, Event_expression,
                                           compileDesign, Reduce::No, event)) {
      event->VpiCondition(exp);
    }
  }  // else @(*) : no event expression
  NodeId Statement_or_null = fC->Sibling(Procedural_timing_control);
  if (VectorOfany* stmts =
          compileStmt(component, fC, Statement_or_null, compileDesign,
                      Reduce::No, event, instance, muteErrors)) {
    event->Stmt((*stmts)[0]);
  }
  return event;
}

UHDM::atomic_stmt* CompileHelper::compileRandcaseStmt(
    DesignComponent* component, const FileContent* fC, NodeId nodeId,
    CompileDesign* compileDesign, UHDM::any* pstmt, ValuedComponentI* instance,
    bool muteErrors) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::atomic_stmt* result = nullptr;
  NodeId RandCase = fC->Child(nodeId);
  UHDM::case_stmt* case_stmt = s.MakeCase_stmt();
  case_stmt->VpiRandType(vpiRand);
  UHDM::VectorOfcase_item* case_items = s.MakeCase_itemVec();
  case_stmt->Case_items(case_items);
  result = case_stmt;
  while (RandCase) {
    NodeId Expression = fC->Child(RandCase);
    UHDM::case_item* case_item = s.MakeCase_item();
    case_items->push_back(case_item);
    VectorOfany* exprs = s.MakeAnyVec();
    case_item->VpiExprs(exprs);
    case_item->VpiParent(case_stmt);
    if (UHDM::any* item_exp =
            compileExpression(component, fC, Expression, compileDesign,
                              Reduce::No, case_item, instance)) {
      setParentNoOverride(item_exp, case_item);
      exprs->push_back(item_exp);
    }
    NodeId stmt = fC->Sibling(Expression);
    if (VectorOfany* stmts =
            compileStmt(component, fC, stmt, compileDesign, Reduce::No,
                        case_item, instance, muteErrors)) {
      case_item->Stmt((*stmts)[0]);
    }
    RandCase = fC->Sibling(RandCase);
    if (fC->Type(RandCase) == VObjectType::paENDCASE) {
      break;
    }
  }
  return result;
}

UHDM::atomic_stmt* CompileHelper::compileCaseStmt(
    DesignComponent* component, const FileContent* fC, NodeId nodeId,
    CompileDesign* compileDesign, UHDM::any* pstmt, ValuedComponentI* instance,
    bool muteErrors) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::atomic_stmt* result = nullptr;
  NodeId Case_keyword = fC->Child(nodeId);
  NodeId Unique;
  if (fC->Type(Case_keyword) == VObjectType::paUnique_priority) {
    Unique = fC->Child(Case_keyword);
    Case_keyword = fC->Sibling(Case_keyword);
  }
  NodeId Case_type = fC->Child(Case_keyword);
  NodeId Condition = fC->Sibling(Case_keyword);
  UHDM::any* cond_exp = compileExpression(
      component, fC, Condition, compileDesign, Reduce::No, pstmt, instance);
  NodeId Case_item = fC->Sibling(Condition);
  UHDM::case_stmt* case_stmt = s.MakeCase_stmt();
  UHDM::VectorOfcase_item* case_items = s.MakeCase_itemVec();
  case_stmt->Case_items(case_items);
  result = case_stmt;
  case_stmt->VpiCondition((UHDM::expr*)cond_exp);
  setParentNoOverride(cond_exp, case_stmt);
  VObjectType CaseType = fC->Type(Case_type);
  switch (CaseType) {
    case VObjectType::paCase_inside_item:
    case VObjectType::paCASE:
      case_stmt->VpiCaseType(vpiCaseExact);
      break;
    case VObjectType::paCASEX:
      case_stmt->VpiCaseType(vpiCaseX);
      break;
    case VObjectType::paCASEZ:
      case_stmt->VpiCaseType(vpiCaseZ);
      break;
    default:
      break;
  }
  if (Unique) {
    VObjectType UniqueType = fC->Type(Unique);
    switch (UniqueType) {
      case VObjectType::paUNIQUE:
        case_stmt->VpiQualifier(vpiUniqueQualifier);
        break;
      case VObjectType::paUNIQUE0:
        case_stmt->VpiQualifier(vpiNoQualifier);
        break;
      case VObjectType::paPRIORITY:
        case_stmt->VpiQualifier(vpiPriorityQualifier);
        break;
      default:
        break;
    }
  }
  while (Case_item) {
    UHDM::case_item* case_item = nullptr;
    if (fC->Type(Case_item) == VObjectType::paCase_item ||
        fC->Type(Case_item) == VObjectType::paCase_inside_item) {
      case_item = s.MakeCase_item();
      case_items->push_back(case_item);
      fC->populateCoreMembers(Case_item, Case_item, case_item);
      case_item->VpiParent(case_stmt);
    }
    bool isDefault = false;
    NodeId Expression;
    if (fC->Type(Case_item) == VObjectType::paCase_item) {
      Expression = fC->Child(Case_item);
      if (fC->Type(Expression) == VObjectType::paExpression) {
        VectorOfany* exprs = s.MakeAnyVec();
        case_item->VpiExprs(exprs);
        while (Expression) {
          if (fC->Type(Expression) == VObjectType::paExpression) {
            // Expr
            if (UHDM::any* item_exp =
                    compileExpression(component, fC, Expression, compileDesign,
                                      Reduce::No, pstmt, instance)) {
              setParentNoOverride(item_exp, case_item);
              exprs->push_back(item_exp);
            }
          } else {
            // Stmt
            if (VectorOfany* stmts =
                    compileStmt(component, fC, Expression, compileDesign,
                                Reduce::No, case_item, instance, muteErrors)) {
              case_item->Stmt((*stmts)[0]);
            }
          }
          Expression = fC->Sibling(Expression);
        }
      } else {
        isDefault = true;
      }
    } else if (fC->Type(Case_item) == VObjectType::paCase_inside_item) {
      NodeId Open_range_list = fC->Child(Case_item);
      if (fC->Type(Open_range_list) == VObjectType::paStatement_or_null) {
        isDefault = true;
        Expression = Open_range_list;
      } else {
        operation* insideOp = s.MakeOperation();
        insideOp->VpiOpType(vpiInsideOp);
        UHDM::VectorOfany* operands = s.MakeAnyVec();
        insideOp->Operands(operands);
        fC->populateCoreMembers(Open_range_list, Open_range_list, insideOp);
        NodeId Value_range = fC->Child(Open_range_list);
        VectorOfany* exprs = s.MakeAnyVec();
        case_item->VpiExprs(exprs);
        exprs->push_back(insideOp);
        insideOp->VpiParent(case_item);

        while (Value_range) {
          if (UHDM::expr* item_exp = (expr*)compileExpression(
                  component, fC, Value_range, compileDesign, Reduce::No,
                  insideOp)) {
            operands->push_back(item_exp);
          }
          Value_range = fC->Sibling(Value_range);
        }
        NodeId Statement_or_null = fC->Sibling(Open_range_list);
        // Stmt
        if (VectorOfany* stmts =
                compileStmt(component, fC, Statement_or_null, compileDesign,
                            Reduce::No, case_item, instance)) {
          case_item->Stmt((*stmts)[0]);
        }
      }
    }

    if (isDefault) {
      // Default
      if (Expression) {
        if (VectorOfany* stmts =
                compileStmt(component, fC, Expression, compileDesign,
                            Reduce::No, case_item, instance)) {
          case_item->Stmt((*stmts)[0]);
        }
      }
    }

    Case_item = fC->Sibling(Case_item);
  }

  return result;
}

std::pair<std::vector<UHDM::io_decl*>*, std::vector<UHDM::variables*>*>
CompileHelper::compileTfPortDecl(DesignComponent* component,
                                 UHDM::task_func* parent, const FileContent* fC,
                                 NodeId tf_item_decl,
                                 CompileDesign* compileDesign) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  std::vector<io_decl*>* ios = parent->Io_decls();
  if (ios == nullptr) ios = s.MakeIo_declVec();
  std::vector<variables*>* vars = parent->Variables();
  if (vars == nullptr) vars = s.MakeVariablesVec();
  std::pair<std::vector<UHDM::io_decl*>*, std::vector<UHDM::variables*>*>
      results = std::make_pair(ios, vars);
  parent->Io_decls(results.first);
  parent->Variables(results.second);
  /*
n<> u<137> t<TfPortDir_Inp> p<141> s<138> l<28>
n<> u<138> t<Data_type_or_implicit> p<141> s<140> l<28>
n<req_1> u<139> t<StringConst> p<140> l<28>
n<> u<140> t<List_of_tf_variable_identifiers> p<141> c<139> l<28>
n<> u<141> t<Tf_port_declaration> p<142> c<137> l<28>
n<> u<142> t<Tf_item_declaration> p<386> c<141> s<384> l<28>
  */
  std::map<std::string, io_decl*, std::less<>> ioMap;

  while (tf_item_decl) {
    if (fC->Type(tf_item_decl) == VObjectType::paTf_item_declaration) {
      NodeId Tf_port_declaration = fC->Child(tf_item_decl);
      if (fC->Type(Tf_port_declaration) == VObjectType::paTf_port_declaration) {
        NodeId TfPortDir = fC->Child(Tf_port_declaration);
        VObjectType tf_port_direction_type = fC->Type(TfPortDir);
        NodeId Data_type_or_implicit = fC->Sibling(TfPortDir);
        NodeId Data_type = fC->Child(Data_type_or_implicit);
        typespec* ts = nullptr;
        if (fC->Type(Data_type) == VObjectType::paData_type) {
          ts = compileTypespec(component, fC, Data_type, compileDesign,
                               Reduce::Yes, parent, nullptr, false);
        } else if (fC->Type(Data_type) == VObjectType::paPacked_dimension) {
          // Implicit type
          logic_typespec* pts = s.MakeLogic_typespec();
          fC->populateCoreMembers(Data_type, Data_type, pts);
          int32_t size;
          if (VectorOfrange* ranges =
                  compileRanges(component, fC, Data_type, compileDesign,
                                Reduce::No, pts, nullptr, size, false)) {
            pts->Ranges(ranges);
          }
          ts = pts;
        }

        NodeId List_of_tf_variable_identifiers =
            fC->Sibling(Data_type_or_implicit);
        NodeId nameId = fC->Child(List_of_tf_variable_identifiers);
        while (nameId) {
          VectorOfrange* ranges = nullptr;
          NodeId Variable_dimension = fC->Sibling(nameId);
          if (fC->Type(Variable_dimension) ==
              VObjectType::paVariable_dimension) {
            int32_t size;
            ranges =
                compileRanges(component, fC, Variable_dimension, compileDesign,
                              Reduce::No, parent, nullptr, size, false);
          }
          const std::string_view name = fC->SymName(nameId);
          io_decl* decl = s.MakeIo_decl();
          ios->push_back(decl);
          decl->VpiParent(parent);
          decl->VpiDirection(
              UhdmWriter::getVpiDirection(tf_port_direction_type));
          decl->VpiName(name);
          ioMap.emplace(name, decl);
          fC->populateCoreMembers(nameId, nameId, decl);
          if (ts != nullptr) {
            if (decl->Typespec() == nullptr) {
              ref_typespec* tsRef = s.MakeRef_typespec();
              tsRef->VpiParent(decl);
              decl->Typespec(tsRef);
            }
            decl->Typespec()->Actual_typespec(ts);
          }
          decl->Ranges(ranges);
          if (fC->Type(Variable_dimension) ==
              VObjectType::paVariable_dimension) {
            nameId = fC->Sibling(nameId);
          }
          nameId = fC->Sibling(nameId);
        }
      } else if (fC->Type(Tf_port_declaration) ==
                 VObjectType::paBlock_item_declaration) {
        NodeId Data_declaration = fC->Child(Tf_port_declaration);
        if (fC->Type(Data_declaration) == VObjectType::paData_declaration) {
          NodeId Variable_declaration = fC->Child(Data_declaration);
          bool is_static = false;
          if (fC->Type(Variable_declaration) ==
              VObjectType::paLifetime_Automatic) {
            Variable_declaration = fC->Sibling(Variable_declaration);
          } else if (fC->Type(Variable_declaration) ==
                     VObjectType::paLifetime_Static) {
            is_static = true;
            Variable_declaration = fC->Sibling(Variable_declaration);
          }
          NodeId Data_type = fC->Child(Variable_declaration);
          UHDM::typespec* ts =
              compileTypespec(component, fC, Data_type, compileDesign,
                              Reduce::No, parent, nullptr, false);
          NodeId List_of_variable_decl_assignments = fC->Sibling(Data_type);
          NodeId Variable_decl_assignment =
              fC->Child(List_of_variable_decl_assignments);
          while (Variable_decl_assignment) {
            NodeId nameId = fC->Child(Variable_decl_assignment);
            const std::string_view name = fC->SymName(nameId);
            std::map<std::string, io_decl*>::iterator itr = ioMap.find(name);
            if (itr == ioMap.end()) {
              if (variables* var = (variables*)compileVariable(
                      component, fC, Data_type, compileDesign, Reduce::No,
                      parent, nullptr, false)) {
                var->VpiAutomatic(!is_static);
                var->VpiName(name);
                vars->push_back(var);
                if (ts != nullptr) {
                  if (var->Typespec() == nullptr) {
                    ref_typespec* tsRef = s.MakeRef_typespec();
                    tsRef->VpiParent(var);
                    var->Typespec(tsRef);
                  }
                  var->Typespec()->Actual_typespec(ts);
                }
              }
            } else if (ts != nullptr) {
              if (itr->second->Typespec() == nullptr) {
                ref_typespec* tsRef = s.MakeRef_typespec();
                tsRef->VpiParent(itr->second);
                itr->second->Typespec(tsRef);
              }
              itr->second->Typespec()->Actual_typespec(ts);
            }
            Variable_decl_assignment = fC->Sibling(Variable_decl_assignment);
          }
        }
      }
    }
    tf_item_decl = fC->Sibling(tf_item_decl);
  }
  return results;
}

std::vector<io_decl*>* CompileHelper::compileTfPortList(
    DesignComponent* component, UHDM::task_func* parent, const FileContent* fC,
    NodeId tf_port_list, CompileDesign* compileDesign) {
  if ((!tf_port_list) ||
      ((fC->Type(tf_port_list) != VObjectType::paTf_port_list) &&
       (fC->Type(tf_port_list) != VObjectType::paLet_port_list))) {
    return nullptr;
  }

  UHDM::Serializer& s = compileDesign->getSerializer();
  std::vector<io_decl*>* ios = s.MakeIo_declVec();
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
  NodeId tf_port_item = fC->Child(tf_port_list);
  int32_t previousDirection = vpiInput;
  UHDM::typespec* ts = nullptr;
  while (tf_port_item) {
    io_decl* decl = s.MakeIo_decl();
    ios->push_back(decl);
    NodeId tf_data_type_or_implicit = fC->Child(tf_port_item);
    NodeId tf_data_type = fC->Child(tf_data_type_or_implicit);
    VObjectType tf_port_direction_type = fC->Type(tf_data_type_or_implicit);
    if (tf_port_direction_type != VObjectType::paData_type_or_implicit)
      previousDirection = UhdmWriter::getVpiDirection(tf_port_direction_type);
    decl->VpiDirection(previousDirection);
    NodeId tf_param_name = fC->Sibling(tf_data_type_or_implicit);
    if (tf_port_direction_type == VObjectType::paTfPortDir_Ref ||
        tf_port_direction_type == VObjectType::paTfPortDir_ConstRef ||
        tf_port_direction_type == VObjectType::paTfPortDir_Inp ||
        tf_port_direction_type == VObjectType::paTfPortDir_Out ||
        tf_port_direction_type == VObjectType::paTfPortDir_Inout) {
      tf_data_type = fC->Sibling(tf_data_type_or_implicit);
      tf_param_name = fC->Sibling(tf_data_type);
    }
    fC->populateCoreMembers(tf_param_name, tf_param_name, decl);
    NodeId type = fC->Child(tf_data_type);
    if (fC->Type(type) == VObjectType::paVIRTUAL) type = fC->Sibling(type);

    NodeId unpackedDimension =
        fC->Sibling(fC->Sibling(fC->Child(tf_port_item)));
    if (unpackedDimension &&
        (fC->Type(unpackedDimension) != VObjectType::paVariable_dimension))
      unpackedDimension = fC->Sibling(unpackedDimension);
    int32_t size;
    if (std::vector<UHDM::range*>* unpackedDimensions =
            compileRanges(component, fC, unpackedDimension, compileDesign,
                          Reduce::No, decl, nullptr, size, false)) {
      decl->Ranges(unpackedDimensions);
    }
    if (UHDM::typespec* tempts =
            compileTypespec(component, fC, type, compileDesign, Reduce::No,
                            decl, nullptr, true)) {
      ts = tempts;
      fC->populateCoreMembers(type, type, ts);
      if (ts->UhdmType() == uhdmunsupported_typespec) {
        component->needLateTypedefBinding(decl);
      }
    }
    decl->VpiParent(parent);

    if (ts != nullptr) {
      if (decl->Typespec() == nullptr) {
        ref_typespec* tsRef = s.MakeRef_typespec();
        tsRef->VpiParent(decl);
        decl->Typespec(tsRef);
      }
      decl->Typespec()->Actual_typespec(ts);
    }

    const std::string_view name = fC->SymName(tf_param_name);
    decl->VpiName(name);

    NodeId expression = fC->Sibling(tf_param_name);
    if (expression &&
        (fC->Type(expression) != VObjectType::paVariable_dimension) &&
        (fC->Type(type) != VObjectType::slStringConst)) {
      if (any* defvalue =
              compileExpression(component, fC, expression, compileDesign,
                                Reduce::No, decl, nullptr)) {
        decl->Expr(defvalue);
      }
    }

    tf_port_item = fC->Sibling(tf_port_item);
  }

  return ios;
}

NodeId CompileHelper::setFuncTaskQualifiers(const FileContent* fC,
                                            NodeId nodeId, task_func* func) {
  NodeId func_decl = nodeId;
  VObjectType func_type = fC->Type(nodeId);

  if (func_type == VObjectType::paFunction_declaration) {
    func_decl = fC->Child(nodeId);
    func_type = fC->Type(func_decl);
  }
  if (func_type == VObjectType::paTask_declaration) {
    func_decl = fC->Child(nodeId);
    func_type = fC->Type(func_decl);
  }

  bool is_local = false;
  bool is_protected = false;
  while ((func_type == VObjectType::paMethodQualifier_Virtual) ||
         (func_type == VObjectType::paMethodQualifier_ClassItem) ||
         (func_type == VObjectType::paPure_virtual_qualifier) ||
         (func_type == VObjectType::paExtern_qualifier) ||
         (func_type == VObjectType::paClassItemQualifier_Protected) ||
         (func_type == VObjectType::paLifetime_Automatic) ||
         (func_type == VObjectType::paLifetime_Static) ||
         (func_type == VObjectType::paDpi_import_export) ||
         (func_type == VObjectType::paPure_keyword) ||
         (func_type == VObjectType::paIMPORT) ||
         (func_type == VObjectType::paEXPORT) ||
         (func_type == VObjectType::paContext_keyword) ||
         (func_type == VObjectType::slStringConst)) {
    if (func_type == VObjectType::paDpi_import_export) {
      func_decl = fC->Child(func_decl);
      func_type = fC->Type(func_decl);
    }
    if (func_type == VObjectType::paPure_keyword) {
      func_decl = fC->Sibling(func_decl);
      func_type = fC->Type(func_decl);
      if (func) func->VpiDPIPure(true);
    }
    if (func_type == VObjectType::paEXPORT) {
      func_decl = fC->Sibling(func_decl);
      func_type = fC->Type(func_decl);
      if (func) func->VpiAccessType(vpiDPIExportAcc);
    }
    if (func_type == VObjectType::paIMPORT) {
      func_decl = fC->Sibling(func_decl);
      func_type = fC->Type(func_decl);
      if (func) func->VpiAccessType(vpiDPIImportAcc);
    }
    if (func_type == VObjectType::slStringLiteral) {
      std::string_view ctype = StringUtils::unquoted(fC->SymName(func_decl));
      if (ctype == "DPI-C") {
        if (func) func->VpiDPICStr(vpiDPIC);
      } else if (ctype == "DPI") {
        if (func) func->VpiDPICStr(vpiDPI);
      }
      func_decl = fC->Sibling(func_decl);
      func_type = fC->Type(func_decl);
    }
    if (func_type == VObjectType::paContext_keyword) {
      func_decl = fC->Sibling(func_decl);
      func_type = fC->Type(func_decl);
      if (func) func->VpiDPIContext(true);
    }
    if (func_type == VObjectType::paMethodQualifier_Virtual) {
      func_decl = fC->Sibling(func_decl);
      func_type = fC->Type(func_decl);
      if (func) func->VpiVirtual(true);
    }
    if (func_type == VObjectType::paLifetime_Automatic) {
      func_decl = fC->Sibling(func_decl);
      func_type = fC->Type(func_decl);
      if (func) func->VpiAutomatic(true);
    }
    if (func_type == VObjectType::paLifetime_Static) {
      func_decl = fC->Sibling(func_decl);
      func_type = fC->Type(func_decl);
    }
    if (func_type == VObjectType::paClassItemQualifier_Protected) {
      is_protected = true;
      if (func) func->VpiVisibility(vpiProtectedVis);
      func_decl = fC->Sibling(func_decl);
      func_type = fC->Type(func_decl);
    }
    if (func_type == VObjectType::paPure_virtual_qualifier) {
      if (func) func->VpiDPIPure(true);
      if (func) func->VpiVirtual(true);
      func_decl = fC->Sibling(func_decl);
      func_type = fC->Type(func_decl);
    }
    if (func_type == VObjectType::paExtern_qualifier) {
      func_decl = fC->Sibling(func_decl);
      func_type = fC->Type(func_decl);
      if (func) func->VpiAccessType(vpiExternAcc);
    }
    if (func_type == VObjectType::paMethodQualifier_ClassItem) {
      NodeId qualifier = fC->Child(func_decl);
      VObjectType type = fC->Type(qualifier);
      if (type == VObjectType::paClassItemQualifier_Static) {
        // TODO: No VPI attribute for static!
      }
      if (type == VObjectType::paClassItemQualifier_Local) {
        if (func) func->VpiVisibility(vpiLocalVis);
        is_local = true;
      }
      if (type == VObjectType::paClassItemQualifier_Protected) {
        is_protected = true;
        if (func) func->VpiVisibility(vpiProtectedVis);
      }
      func_decl = fC->Sibling(func_decl);
      func_type = fC->Type(func_decl);
    }
  }
  if ((!is_local) && (!is_protected)) {
    if (func) func->VpiVisibility(vpiPublicVis);
  }
  return func_decl;
}

bool CompileHelper::compileTask(DesignComponent* component,
                                const FileContent* fC, NodeId nodeId,
                                CompileDesign* compileDesign, Reduce reduce,
                                ValuedComponentI* instance, bool isMethod) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  std::vector<UHDM::task_func*>* task_funcs = component->getTask_funcs();
  if (task_funcs == nullptr) {
    component->setTask_funcs(s.MakeTask_funcVec());
    task_funcs = component->getTask_funcs();
  }
  std::string name;
  NodeId task_decl = setFuncTaskQualifiers(fC, nodeId, nullptr);
  NodeId Task_body_declaration;
  if (fC->Type(task_decl) == VObjectType::paTask_body_declaration)
    Task_body_declaration = task_decl;
  else
    Task_body_declaration = fC->Child(task_decl);
  NodeId task_name = fC->Child(Task_body_declaration);
  if (fC->Type(task_name) == VObjectType::slStringConst)
    name = fC->SymName(task_name);
  else if (fC->Type(task_name) == VObjectType::paClass_scope) {
    NodeId Class_type = fC->Child(task_name);
    name.assign(fC->SymName(fC->Child(Class_type)))
        .append("::")
        .append(fC->SymName(fC->Sibling(task_name)));
    task_name = fC->Sibling(task_name);
  }

  UHDM::task* task = nullptr;
  for (auto f : *component->getTask_funcs()) {
    if (f->VpiName() == name) {
      task = reinterpret_cast<UHDM::task*>(f);
      break;
    }
  }
  if (task == nullptr) {
    // make placeholder first
    task = s.MakeTask();
    task->VpiName(name);
    fC->populateCoreMembers(task_decl, task_decl, task);
    task_funcs->push_back(task);
    return true;
  }
  if (task->Io_decls() || task->Variables() || task->Stmt()) return true;
  setFuncTaskQualifiers(fC, nodeId, task);
  task->VpiMethod(isMethod);
  fC->populateCoreMembers(nodeId, task_decl, task);
  NodeId Tf_port_list = fC->Sibling(task_name);
  NodeId Statement_or_null;
  if (fC->Type(Tf_port_list) == VObjectType::paTf_port_list) {
    Statement_or_null = fC->Sibling(Tf_port_list);
    task->Io_decls(
        compileTfPortList(component, task, fC, Tf_port_list, compileDesign));
  } else if (fC->Type(Tf_port_list) == VObjectType::paTf_item_declaration) {
    NodeId Block_item_declaration = fC->Child(Tf_port_list);
    if (fC->Type(Block_item_declaration) !=
        VObjectType::paBlock_item_declaration) {
      compileTfPortDecl(component, task, fC, Tf_port_list, compileDesign);
      while (fC->Type(Tf_port_list) == VObjectType::paTf_item_declaration) {
        NodeId Tf_port_declaration = fC->Child(Tf_port_list);
        if (fC->Type(Tf_port_declaration) ==
            VObjectType::paTf_port_declaration) {
        } else if (fC->Type(Tf_port_declaration) ==
                   VObjectType::paBlock_item_declaration) {
          NodeId ItemNode = fC->Child(Tf_port_declaration);
          if (fC->Type(ItemNode) != VObjectType::paData_declaration) break;
        } else {
          break;
        }
        Tf_port_list = fC->Sibling(Tf_port_list);
      }
    }
    Statement_or_null = Tf_port_list;
  } else if (fC->Type(Tf_port_list) == VObjectType::paBlock_item_declaration) {
    Statement_or_null = Tf_port_list;
  } else {
    if (fC->Type(Tf_port_list) == VObjectType::paStatement_or_null)
      Statement_or_null = Tf_port_list;
  }

  NodeId MoreStatement_or_null = fC->Sibling(Statement_or_null);
  if (MoreStatement_or_null &&
      (fC->Type(MoreStatement_or_null) == VObjectType::paENDTASK)) {
    MoreStatement_or_null = InvalidNodeId;
  }
  if (MoreStatement_or_null) {
    // Page 983, 2017 Standard: More than 1 Stmts
    begin* begin = s.MakeBegin();
    task->Stmt(begin);
    begin->VpiParent(task);
    fC->populateCoreMembers(MoreStatement_or_null, MoreStatement_or_null,
                            begin);
    VectorOfany* stmts = s.MakeAnyVec();
    begin->Stmts(stmts);
    while (Statement_or_null) {
      if (Statement_or_null &&
          (fC->Type(Statement_or_null) == VObjectType::paENDTASK))
        break;
      if (fC->Type(fC->Child(Statement_or_null)) ==
          VObjectType::paTf_port_declaration) {
        compileTfPortDecl(component, task, fC, Statement_or_null,
                          compileDesign);
        while (fC->Type(Statement_or_null) ==
               VObjectType::paTf_item_declaration) {
          NodeId Tf_port_declaration = fC->Child(Statement_or_null);
          if (fC->Type(Tf_port_declaration) ==
              VObjectType::paTf_port_declaration) {
          } else if (fC->Type(Tf_port_declaration) ==
                     VObjectType::paBlock_item_declaration) {
            NodeId ItemNode = fC->Child(Tf_port_declaration);
            if (fC->Type(ItemNode) != VObjectType::paData_declaration) break;
          } else {
            break;
          }
          Statement_or_null = fC->Sibling(Statement_or_null);
        }
      } else {
        if (VectorOfany* sts =
                compileStmt(component, fC, Statement_or_null, compileDesign,
                            reduce, begin, instance)) {
          for (any* st : *sts) {
            UHDM_OBJECT_TYPE stmt_type = st->UhdmType();
            if (stmt_type == uhdmparam_assign) {
              UHDM::VectorOfparam_assign* param_assigns = task->Param_assigns();
              if (param_assigns == nullptr) {
                task->Param_assigns(s.MakeParam_assignVec());
                param_assigns = task->Param_assigns();
              }
              if (param_assign* pst = any_cast<param_assign*>(st))
                param_assigns->push_back(pst);
            }
            if (stmt_type == uhdmassignment) {
              assignment* stmt = (assignment*)st;
              if (stmt->Rhs() == nullptr || any_cast<variables*>(stmt->Lhs())) {
                // Declaration
                VectorOfvariables* vars = task->Variables();
                if (vars == nullptr) {
                  task->Variables(s.MakeVariablesVec());
                  vars = task->Variables();
                }
                if (stmt->Lhs()) vars->push_back((variables*)stmt->Lhs());
                if (stmt->Rhs() != nullptr) {
                  stmts->push_back(st);
                } else {
                  if (variables* var = any_cast<variables*>(stmt->Lhs()))
                    var->VpiParent(begin);
                  // s.Erase(stmt);
                }
              } else {
                stmts->push_back(st);
              }
            } else {
              stmts->push_back(st);
            }
            st->VpiParent(begin);
          }
        }
      }
      Statement_or_null = fC->Sibling(Statement_or_null);
    }
  } else {
    // Page 983, 2017 Standard: 0 or 1 Stmt
    if (Statement_or_null &&
        (fC->Type(Statement_or_null) != VObjectType::paENDTASK)) {
      VectorOfany* stmts = compileStmt(component, fC, Statement_or_null,
                                       compileDesign, reduce, task, instance);
      if (stmts) {
        for (any* st : *stmts) {
          UHDM_OBJECT_TYPE stmt_type = st->UhdmType();
          if (stmt_type == uhdmparam_assign) {
            UHDM::VectorOfparam_assign* param_assigns = task->Param_assigns();
            if (param_assigns == nullptr) {
              task->Param_assigns(s.MakeParam_assignVec());
              param_assigns = task->Param_assigns();
            }
            if (param_assign* pst = any_cast<param_assign*>(st))
              param_assigns->push_back(pst);
          } else if (stmt_type == uhdmassignment) {
            assignment* stmt = (assignment*)st;
            if (stmt->Rhs() == nullptr || any_cast<variables*>(stmt->Lhs())) {
              // Declaration
              VectorOfvariables* vars = task->Variables();
              if (vars == nullptr) {
                task->Variables(s.MakeVariablesVec());
                vars = task->Variables();
              }
              if (stmt->Lhs()) vars->push_back((variables*)stmt->Lhs());
              if (stmt->Rhs() != nullptr) {
                task->Stmt(st);
              } else {
                if (variables* var = any_cast<variables*>(stmt->Lhs()))
                  var->VpiParent(task);
                // s.Erase(stmt);
              }
            } else {
              task->Stmt(st);
            }
          } else {
            task->Stmt(st);
          }
          st->VpiParent(task);
        }
      }
    }
  }
  return true;
}

bool CompileHelper::compileClassConstructorDeclaration(
    DesignComponent* component, const FileContent* fC, NodeId nodeId,
    CompileDesign* compileDesign) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  std::vector<UHDM::task_func*>* task_funcs = component->getTask_funcs();
  if (task_funcs == nullptr) {
    component->setTask_funcs(s.MakeTask_funcVec());
    task_funcs = component->getTask_funcs();
  }
  UHDM::function* func = s.MakeFunction();
  func->VpiMethod(true);
  task_funcs->push_back(func);
  fC->populateCoreMembers(nodeId, nodeId, func);
  std::string name = "new";
  std::string className;
  NodeId Tf_port_list;
  Tf_port_list = fC->Child(nodeId);
  if (fC->Type(Tf_port_list) == VObjectType::paClass_scope) {
    NodeId Class_scope = Tf_port_list;
    NodeId Class_type = fC->Child(Class_scope);
    NodeId Class_name = fC->Child(Class_type);
    name = fC->SymName(Class_name);
    className = name;
    name += "::new";
    Tf_port_list = fC->Sibling(Tf_port_list);
  }
  UHDM::class_var* var = s.MakeClass_var();
  var->VpiParent(func);
  func->Return(var);
  UHDM::class_typespec* tps = s.MakeClass_typespec();
  ref_typespec* tpsRef = s.MakeRef_typespec();
  tpsRef->VpiParent(var);
  tpsRef->Actual_typespec(tps);
  var->Typespec(tpsRef);
  NodeId tf_Port_ItemId = fC->Child(Tf_port_list);
  NodeId data_type_or_implicitId = fC->Child(tf_Port_ItemId);
  NodeId varId = fC->Sibling(data_type_or_implicitId);
  if (varId) fC->populateCoreMembers(varId, varId, var);
  if (ClassDefinition* cdef =
          valuedcomponenti_cast<ClassDefinition*>(component)) {
    tps->Class_defn(cdef->getUhdmDefinition());
    const std::string_view name = cdef->getUhdmDefinition()->VpiName();
    tps->VpiName(name);
  } else if (Package* p = valuedcomponenti_cast<Package*>(component)) {
    if (ClassDefinition* cdef = p->getClassDefinition(className)) {
      const std::string_view name = cdef->getUhdmDefinition()->VpiName();
      tps->Class_defn(cdef->getUhdmDefinition());
      tps->VpiName(name);
    }
  }

  func->VpiName(name);
  func->Io_decls(
      compileTfPortList(component, func, fC, Tf_port_list, compileDesign));

  NodeId Stmt;
  if (fC->Type(Tf_port_list) == VObjectType::paFunction_statement_or_null) {
    Stmt = Tf_port_list;
  } else {
    Stmt = fC->Sibling(Tf_port_list);
  }
  int32_t nbStmts = 0;
  NodeId StmtTmp = Stmt;
  while (StmtTmp) {
    if (fC->Type(StmtTmp) == VObjectType::paBlock_item_declaration) {
      nbStmts++;
    } else if (fC->Type(StmtTmp) == VObjectType::paSuper_dot_new) {
      nbStmts++;
      NodeId lookAhead = fC->Sibling(StmtTmp);
      if (fC->Type(lookAhead) == VObjectType::paList_of_arguments) {
        StmtTmp = fC->Sibling(StmtTmp);
      }
    } else if (fC->Type(StmtTmp) == VObjectType::paFunction_statement_or_null) {
      nbStmts++;
    }
    StmtTmp = fC->Sibling(StmtTmp);
  }

  if (nbStmts == 1) {
    if (fC->Type(Stmt) == VObjectType::paSuper_dot_new) {
      UHDM::method_func_call* mcall = s.MakeMethod_func_call();
      mcall->VpiParent(func);
      mcall->VpiName("super.new");
      NodeId Args = fC->Sibling(Stmt);
      if (fC->Type(Args) == VObjectType::paList_of_arguments) {
        VectorOfany* arguments =
            compileTfCallArguments(component, fC, Args, compileDesign,
                                   Reduce::No, mcall, nullptr, false);
        mcall->Tf_call_args(arguments);
        Stmt = fC->Sibling(Stmt);  // NOLINT(*.DeadStores)
      }
      func->Stmt(mcall);
    } else {
      NodeId Statement = fC->Child(Stmt);
      if (Statement) {
        VectorOfany* sts = compileStmt(component, fC, Statement, compileDesign,
                                       Reduce::No, func);
        if (sts) {
          any* st = (*sts)[0];
          st->VpiParent(func);
          func->Stmt(st);
        }
      }
    }
  } else if (nbStmts > 1) {
    begin* begin = s.MakeBegin();
    func->Stmt(begin);
    begin->VpiParent(func);
    VectorOfany* stmts = s.MakeAnyVec();
    begin->Stmts(stmts);
    Stmt = fC->Sibling(Tf_port_list);
    while (Stmt) {
      if (fC->Type(Stmt) == VObjectType::paSuper_dot_new) {
        UHDM::method_func_call* mcall = s.MakeMethod_func_call();
        mcall->VpiParent(func);
        mcall->VpiName("super.new");
        NodeId Args = fC->Sibling(Stmt);
        if (fC->Type(Args) == VObjectType::paList_of_arguments) {
          VectorOfany* arguments =
              compileTfCallArguments(component, fC, Args, compileDesign,
                                     Reduce::No, mcall, nullptr, false);
          mcall->Tf_call_args(arguments);
          Stmt = fC->Sibling(Stmt);
        }
        stmts->push_back(mcall);
        mcall->VpiParent(begin);
      } else {
        NodeId Statement = fC->Child(Stmt);
        if (Statement) {
          if (VectorOfany* sts = compileStmt(
                  component, fC, Statement, compileDesign, Reduce::No, begin)) {
            for (any* st : *sts) {
              stmts->push_back(st);
              st->VpiParent(begin);
            }
          }
        }
      }
      Stmt = fC->Sibling(Stmt);
    }
  }

  return true;
}

bool CompileHelper::compileFunction(DesignComponent* component,
                                    const FileContent* fC, NodeId nodeId,
                                    CompileDesign* compileDesign, Reduce reduce,
                                    ValuedComponentI* instance, bool isMethod) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  std::vector<UHDM::task_func*>* task_funcs = component->getTask_funcs();
  if (task_funcs == nullptr) {
    component->setTask_funcs(s.MakeTask_funcVec());
    task_funcs = component->getTask_funcs();
  }
  std::string name;
  NodeId func_decl = setFuncTaskQualifiers(fC, nodeId, nullptr);
  VObjectType func_decl_type = fC->Type(func_decl);
  bool constructor = false;
  if (func_decl_type == VObjectType::paClass_constructor_declaration ||
      func_decl_type == VObjectType::paClass_constructor_prototype) {
    constructor = true;
  }
  NodeId Tf_port_list;
  if (constructor) {
    Tf_port_list = fC->Child(func_decl);
    name = "new";
  } else {
    NodeId Function_body_declaration;
    if (fC->Type(func_decl) == VObjectType::paFunction_body_declaration)
      Function_body_declaration = func_decl;
    else
      Function_body_declaration = fC->Child(func_decl);
    NodeId Function_data_type_or_implicit =
        fC->Child(Function_body_declaration);
    NodeId Function_name = fC->Sibling(Function_data_type_or_implicit);
    if (fC->Type(Function_name) == VObjectType::slStringConst) {
      name = fC->SymName(Function_name);
      Tf_port_list = fC->Sibling(Function_name);
    } else if (fC->Type(Function_name) == VObjectType::paClass_scope) {
      NodeId Class_type = fC->Child(Function_name);
      NodeId suffixname = fC->Sibling(Function_name);
      name.assign(fC->SymName(fC->Child(Class_type)))
          .append("::")
          .append(fC->SymName(suffixname));
      Tf_port_list = fC->Sibling(suffixname);
    }
  }
  UHDM::function* func = nullptr;
  for (auto f : *component->getTask_funcs()) {
    if (f->VpiName() == name) {
      func = any_cast<UHDM::function*>(f);
      break;
    }
  }
  if (func == nullptr) {
    // make placeholder first
    func = s.MakeFunction();
    func->VpiName(name);
    fC->populateCoreMembers(nodeId, nodeId, func);
    task_funcs->push_back(func);
    return true;
  }
  if (func->Io_decls() || func->Variables() || func->Stmt()) return true;
  setFuncTaskQualifiers(fC, nodeId, func);
  func->VpiMethod(isMethod);
  if (constructor) {
    UHDM::class_var* var = s.MakeClass_var();
    var->VpiParent(func);
    func->Return(var);
    UHDM::class_typespec* tps = s.MakeClass_typespec();
    ref_typespec* tpsRef = s.MakeRef_typespec();
    tpsRef->VpiParent(var);
    tpsRef->Actual_typespec(tps);
    var->Typespec(tpsRef);
    ClassDefinition* cdef = valuedcomponenti_cast<ClassDefinition*>(component);
    tps->Class_defn(cdef->getUhdmDefinition());
    tps->VpiName(cdef->getUhdmDefinition()->VpiFullName());
  } else {
    NodeId Function_body_declaration;
    if (fC->Type(func_decl) == VObjectType::paFunction_body_declaration)
      Function_body_declaration = func_decl;
    else
      Function_body_declaration = fC->Child(func_decl);
    NodeId Function_data_type_or_implicit =
        fC->Child(Function_body_declaration);
    NodeId Function_data_type = fC->Child(Function_data_type_or_implicit);
    NodeId Return_data_type = fC->Child(Function_data_type);
    if (fC->Type(Function_data_type) == VObjectType::paPacked_dimension) {
      Return_data_type = Function_data_type;
    }
    if ((!Return_data_type) &&
        ((fC->Type(Function_data_type) == VObjectType::paSigning_Unsigned) ||
         (fC->Type(Function_data_type) == VObjectType::paSigning_Signed))) {
      Return_data_type = Function_data_type;
    }
    variables* var = nullptr;
    if (Return_data_type) {
      var = any_cast<variables*>(
          compileVariable(component, fC, Return_data_type, compileDesign,
                          Reduce::No, nullptr, instance, false));
      if (var) {
        // Explicit return type
        var->VpiName("");
      }
    } else if (!Function_data_type) {
      // Implicit return type
      var = s.MakeLogic_var();
    }  // else void return type
    if (var != nullptr) {
      var->VpiParent(func);
      func->Return(var);
    }
  }

  NodeId Function_statement_or_null = Tf_port_list;
  if (fC->Type(Tf_port_list) == VObjectType::paTf_port_list) {
    func->Io_decls(
        compileTfPortList(component, func, fC, Tf_port_list, compileDesign));
    Function_statement_or_null = fC->Sibling(Tf_port_list);
  } else if (fC->Type(Tf_port_list) == VObjectType::paTf_item_declaration) {
    auto results =
        compileTfPortDecl(component, func, fC, Tf_port_list, compileDesign);
    func->Io_decls(results.first);
    func->Variables(results.second);
    while (fC->Type(Tf_port_list) == VObjectType::paTf_item_declaration) {
      NodeId Block_item_declaration = fC->Child(Tf_port_list);
      NodeId Parameter_declaration = fC->Child(Block_item_declaration);
      if ((fC->Type(Parameter_declaration) ==
           VObjectType::paParameter_declaration) ||
          (fC->Type(Parameter_declaration) ==
           VObjectType::paLocal_parameter_declaration)) {
        DesignComponent* tmp =
            new ModuleDefinition(nullptr, InvalidNodeId, "fake");
        compileParameterDeclaration(
            tmp, fC, Parameter_declaration, compileDesign, Reduce::No,
            (fC->Type(Parameter_declaration) ==
             VObjectType::paLocal_parameter_declaration),
            nullptr, false, false);
        if (tmp->getParameters()) {
          VectorOfany* params = func->Parameters();
          if (params == nullptr) {
            func->Parameters(s.MakeAnyVec());
            params = func->Parameters();
          }
          for (auto p : *tmp->getParameters()) {
            params->push_back(p);
          }
        }
        if (tmp->getParam_assigns()) {
          VectorOfparam_assign* params = func->Param_assigns();
          if (params == nullptr) {
            func->Param_assigns(s.MakeParam_assignVec());
            params = func->Param_assigns();
          }
          for (auto p : *tmp->getParam_assigns()) {
            p->VpiParent(func);
            params->push_back(p);
          }
        }
        delete tmp;
      }

      Tf_port_list = fC->Sibling(Tf_port_list);
    }
    Function_statement_or_null = Tf_port_list;
  }

  NodeId MoreFunction_statement_or_null =
      fC->Sibling(Function_statement_or_null);
  if (MoreFunction_statement_or_null &&
      (fC->Type(MoreFunction_statement_or_null) ==
       VObjectType::paENDFUNCTION)) {
    MoreFunction_statement_or_null = InvalidNodeId;
  }
  if (MoreFunction_statement_or_null) {
    // Page 983, 2017 Standard: More than 1 Stmts
    begin* begin = s.MakeBegin();
    func->Stmt(begin);
    begin->VpiParent(func);
    VectorOfany* stmts = s.MakeAnyVec();
    begin->Stmts(stmts);
    fC->populateCoreMembers(MoreFunction_statement_or_null,
                            MoreFunction_statement_or_null, begin);
    while (Function_statement_or_null) {
      NodeId Statement = fC->Child(Function_statement_or_null);
      if (Statement) {
        if (VectorOfany* sts =
                compileStmt(component, fC, Statement, compileDesign, reduce,
                            begin, instance)) {
          for (any* st : *sts) {
            UHDM_OBJECT_TYPE stmt_type = st->UhdmType();
            if (stmt_type == uhdmparam_assign) {
              UHDM::VectorOfparam_assign* param_assigns = func->Param_assigns();
              if (param_assigns == nullptr) {
                func->Param_assigns(s.MakeParam_assignVec());
                param_assigns = func->Param_assigns();
              }
              if (param_assign* pst = any_cast<param_assign*>(st))
                param_assigns->push_back(pst);
            } else if (stmt_type == uhdmassignment) {
              assignment* stmt = (assignment*)st;
              if (stmt->Rhs() == nullptr || any_cast<variables*>(stmt->Lhs())) {
                // Declaration
                VectorOfvariables* vars = func->Variables();
                if (vars == nullptr) {
                  func->Variables(s.MakeVariablesVec());
                  vars = func->Variables();
                }
                if (stmt->Lhs()) vars->push_back((variables*)stmt->Lhs());
                if (stmt->Rhs() != nullptr) {
                  stmts->push_back(st);
                } else {
                  if (variables* var = any_cast<variables*>(stmt->Lhs()))
                    var->VpiParent(begin);
                  // s.Erase(stmt);
                }
              } else {
                stmts->push_back(st);
              }
            } else {
              stmts->push_back(st);
            }
            st->VpiParent(begin);
          }
        }
      }
      Function_statement_or_null = fC->Sibling(Function_statement_or_null);
    }
  } else {
    // Page 983, 2017 Standard: 0 or 1 Stmt
    NodeId Statement = fC->Child(Function_statement_or_null);
    if (Statement) {
      VectorOfany* sts = compileStmt(component, fC, Statement, compileDesign,
                                     reduce, func, instance);
      if (sts) {
        any* st = (*sts)[0];
        UHDM_OBJECT_TYPE stmt_type = st->UhdmType();
        if (stmt_type == uhdmparam_assign) {
          UHDM::VectorOfparam_assign* param_assigns = func->Param_assigns();
          if (param_assigns == nullptr) {
            func->Param_assigns(s.MakeParam_assignVec());
            param_assigns = func->Param_assigns();
          }
          if (param_assign* pst = any_cast<param_assign*>(st))
            param_assigns->push_back(pst);
        } else if (stmt_type == uhdmassignment) {
          assignment* stmt = (assignment*)st;
          if (stmt->Rhs() == nullptr || any_cast<variables*>(stmt->Lhs())) {
            // Declaration
            VectorOfvariables* vars = func->Variables();
            if (vars == nullptr) {
              func->Variables(s.MakeVariablesVec());
              vars = func->Variables();
            }
            if (stmt->Lhs()) vars->push_back((variables*)stmt->Lhs());
            if (stmt->Rhs() != nullptr) {
              func->Stmt(st);
            } else {
              if (variables* var = any_cast<variables*>(stmt->Lhs()))
                var->VpiParent(func);
              // s.Erase(stmt);
            }
          } else {
            func->Stmt(st);
          }
        } else {
          func->Stmt(st);
        }
        st->VpiParent(func);
      }
    }
  }
  return true;
}

Task* CompileHelper::compileTaskPrototype(DesignComponent* scope,
                                          const FileContent* fC, NodeId id,
                                          CompileDesign* compileDesign) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  std::vector<UHDM::task_func*>* task_funcs = scope->getTask_funcs();
  if (task_funcs == nullptr) {
    scope->setTask_funcs(s.MakeTask_funcVec());
    task_funcs = scope->getTask_funcs();
  }
  UHDM::task* task = s.MakeTask();
  task_funcs->push_back(task);
  NodeId prop = setFuncTaskQualifiers(fC, id, task);
  NodeId task_prototype = prop;
  NodeId task_name = fC->Child(task_prototype);
  std::string taskName(fC->SymName(task_name));
  fC->populateCoreMembers(id, id, task);
  NodeId Tf_port_list;
  if (fC->Type(task_name) == VObjectType::slStringConst) {
    Tf_port_list = fC->Sibling(task_name);
  } else if (fC->Type(task_name) == VObjectType::paClass_scope) {
    NodeId Class_type = fC->Child(task_name);
    NodeId suffixname = fC->Sibling(task_name);
    taskName.assign(fC->SymName(fC->Child(Class_type)))
        .append("::")
        .append(fC->SymName(suffixname));
    Tf_port_list = fC->Sibling(suffixname);
  }

  task->VpiName(taskName);

  if (fC->Type(Tf_port_list) == VObjectType::paTf_port_list) {
    task->Io_decls(
        compileTfPortList(scope, task, fC, Tf_port_list, compileDesign));
  } else if (fC->Type(Tf_port_list) == VObjectType::paTf_item_declaration) {
    auto results =
        compileTfPortDecl(scope, task, fC, Tf_port_list, compileDesign);
    task->Io_decls(results.first);
  }

  Task* result = new Task(scope, fC, id, taskName);
  result->compile(*this);
  return result;
}

Function* CompileHelper::compileFunctionPrototype(
    DesignComponent* scope, const FileContent* fC, NodeId id,
    CompileDesign* compileDesign) {
  std::string funcName;
  NodeId function_name;
  UHDM::Serializer& s = compileDesign->getSerializer();
  std::vector<UHDM::task_func*>* task_funcs = scope->getTask_funcs();
  if (task_funcs == nullptr) {
    scope->setTask_funcs(s.MakeTask_funcVec());
    task_funcs = scope->getTask_funcs();
  }
  UHDM::function* func = s.MakeFunction();
  task_funcs->push_back(func);
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
  NodeId prop = setFuncTaskQualifiers(fC, id, func);
  NodeId func_prototype = prop;
  NodeId function_data_type = fC->Child(func_prototype);
  NodeId data_type = fC->Child(function_data_type);
  NodeId type = fC->Child(data_type);
  VObjectType the_type = fC->Type(type);
  std::string typeName;
  if (the_type == VObjectType::slStringConst) {
    typeName = fC->SymName(type);
  } else if (the_type == VObjectType::paClass_scope) {
    NodeId class_type = fC->Child(type);
    NodeId class_name = fC->Child(class_type);
    typeName = fC->SymName(class_name);
    typeName += "::";
    NodeId symb_id = fC->Sibling(type);
    typeName += fC->SymName(symb_id);
  } else {
    typeName = VObject::getTypeName(the_type);
  }

  if (fC->Type(fC->Child(id)) == VObjectType::paEXPORT) {
    function_name = fC->Child(func_prototype);
    funcName = fC->SymName(function_name);
  } else if (fC->Type(fC->Child(id)) == VObjectType::paIMPORT) {
    function_name = fC->Sibling(function_data_type);
    funcName = fC->SymName(function_name);
  }

  fC->populateCoreMembers(id, id, func);
  if (auto v = any_cast<variables*>(compileVariable(scope, fC, type,
                                                    compileDesign, Reduce::Yes,
                                                    nullptr, nullptr, false))) {
    v->VpiParent(func);
    func->Return(v);
  }
  NodeId Tf_port_list;
  if (fC->Type(function_name) == VObjectType::slStringConst) {
    Tf_port_list = fC->Sibling(function_name);
  } else if (fC->Type(function_name) == VObjectType::paClass_scope) {
    NodeId Class_type = fC->Child(function_name);
    NodeId suffixname = fC->Sibling(function_name);
    funcName.assign(fC->SymName(fC->Child(Class_type)))
        .append("::")
        .append(fC->SymName(suffixname));
    Tf_port_list = fC->Sibling(suffixname);
  }

  func->VpiName(funcName);

  if (fC->Type(Tf_port_list) == VObjectType::paTf_port_list) {
    func->Io_decls(
        compileTfPortList(scope, func, fC, Tf_port_list, compileDesign));
  } else if (fC->Type(Tf_port_list) == VObjectType::paTf_item_declaration) {
    auto results =
        compileTfPortDecl(scope, func, fC, Tf_port_list, compileDesign);
    func->Io_decls(results.first);
  }

  DataType* returnType = new DataType();
  returnType->init(fC, type, typeName, fC->Type(type));
  Function* result = new Function(scope, fC, id, funcName, returnType);
  Variable* variable =
      new Variable(returnType, fC, id, InvalidNodeId, funcName);
  result->addVariable(variable);
  result->compile(*this);
  return result;
}

UHDM::any* CompileHelper::compileProceduralContinuousAssign(
    DesignComponent* component, const FileContent* fC, NodeId nodeId,
    CompileDesign* compileDesign) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  NodeId assigntypeid = fC->Child(nodeId);
  VObjectType assigntype = fC->Type(assigntypeid);
  UHDM::atomic_stmt* the_stmt = nullptr;
  switch (assigntype) {
    case VObjectType::paASSIGN: {
      assign_stmt* assign = s.MakeAssign_stmt();
      NodeId Variable_assignment = fC->Sibling(assigntypeid);
      NodeId Variable_lvalue = fC->Child(Variable_assignment);
      NodeId Hierarchical_identifier = fC->Child(Variable_lvalue);
      if (fC->Type(fC->Child(Hierarchical_identifier)) ==
          VObjectType::paHierarchical_identifier) {
        Hierarchical_identifier = fC->Child(fC->Child(Hierarchical_identifier));
      } else if (fC->Type(Hierarchical_identifier) !=
                 VObjectType::paPs_or_hierarchical_identifier) {
        Hierarchical_identifier = Variable_lvalue;
      }
      NodeId Expression = fC->Sibling(Variable_lvalue);
      expr* lhs = (expr*)compileExpression(
          component, fC, Hierarchical_identifier, compileDesign, Reduce::No);
      if (lhs) lhs->VpiParent(assign);
      expr* rhs = (expr*)compileExpression(component, fC, Expression,
                                           compileDesign, Reduce::No);
      if (rhs) rhs->VpiParent(assign);
      assign->Lhs(lhs);
      assign->Rhs(rhs);
      the_stmt = assign;
      break;
    }
    case VObjectType::paFORCE: {
      force* assign = s.MakeForce();
      NodeId Variable_assignment = fC->Sibling(assigntypeid);
      NodeId Variable_lvalue = fC->Child(Variable_assignment);
      NodeId Hierarchical_identifier = fC->Child(Variable_lvalue);
      if (fC->Type(fC->Child(Hierarchical_identifier)) ==
          VObjectType::paHierarchical_identifier) {
        Hierarchical_identifier = fC->Child(fC->Child(Hierarchical_identifier));
      } else if (fC->Type(Hierarchical_identifier) !=
                 VObjectType::paPs_or_hierarchical_identifier) {
        Hierarchical_identifier = Variable_lvalue;
      }
      NodeId Expression = fC->Sibling(Variable_lvalue);
      expr* lhs = (expr*)compileExpression(
          component, fC, Hierarchical_identifier, compileDesign, Reduce::No);
      if (lhs) lhs->VpiParent(assign);
      expr* rhs = (expr*)compileExpression(component, fC, Expression,
                                           compileDesign, Reduce::No);
      if (rhs) rhs->VpiParent(assign);
      assign->Lhs(lhs);
      assign->Rhs(rhs);
      the_stmt = assign;
      break;
    }
    case VObjectType::paDEASSIGN: {
      deassign* assign = s.MakeDeassign();
      NodeId Variable_assignment = fC->Sibling(assigntypeid);
      NodeId Variable_lvalue = fC->Child(Variable_assignment);
      NodeId Hierarchical_identifier = fC->Child(Variable_lvalue);
      if (fC->Type(fC->Child(Hierarchical_identifier)) ==
          VObjectType::paHierarchical_identifier) {
        Hierarchical_identifier = fC->Child(fC->Child(Hierarchical_identifier));
      } else if (fC->Type(Hierarchical_identifier) !=
                 VObjectType::paPs_or_hierarchical_identifier) {
        Hierarchical_identifier = Variable_lvalue;
      }
      expr* lhs = (expr*)compileExpression(
          component, fC, Hierarchical_identifier, compileDesign, Reduce::No);
      if (lhs) lhs->VpiParent(assign);
      assign->Lhs(lhs);
      the_stmt = assign;
      break;
    }
    case VObjectType::paRELEASE: {
      release* assign = s.MakeRelease();
      NodeId Variable_assignment = fC->Sibling(assigntypeid);
      NodeId Variable_lvalue = fC->Child(Variable_assignment);
      NodeId Hierarchical_identifier = fC->Child(Variable_lvalue);
      if (fC->Type(fC->Child(Hierarchical_identifier)) ==
          VObjectType::paHierarchical_identifier) {
        Hierarchical_identifier = fC->Child(fC->Child(Hierarchical_identifier));
      } else if (fC->Type(Hierarchical_identifier) !=
                 VObjectType::paPs_or_hierarchical_identifier) {
        Hierarchical_identifier = Variable_lvalue;
      }
      expr* lhs = (expr*)compileExpression(
          component, fC, Hierarchical_identifier, compileDesign, Reduce::No);
      if (lhs) lhs->VpiParent(assign);
      assign->Lhs(lhs);
      the_stmt = assign;
      break;
    }
    default:
      break;
  }
  return the_stmt;
}

UHDM::any* CompileHelper::compileForLoop(DesignComponent* component,
                                         const FileContent* fC, NodeId nodeId,
                                         CompileDesign* compileDesign,
                                         bool muteErrors) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  for_stmt* for_stmt = s.MakeFor_stmt();
  NodeId For_initialization;
  NodeId Condition;
  NodeId For_step;
  NodeId Statement_or_null;
  NodeId tmp = fC->Sibling(nodeId);
  while (tmp) {
    if (fC->Type(tmp) == VObjectType::paFor_initialization) {
      For_initialization = tmp;
    } else if (fC->Type(tmp) == VObjectType::paExpression) {
      Condition = tmp;
    } else if (fC->Type(tmp) == VObjectType::paFor_step) {
      For_step = tmp;
    } else if (fC->Type(tmp) == VObjectType::paStatement_or_null) {
      Statement_or_null = tmp;
    }
    tmp = fC->Sibling(tmp);
  }

  // Init
  if (For_initialization) {
    NodeId For_variable_declaration = fC->Child(For_initialization);
    if (fC->Type(For_variable_declaration) ==
        VObjectType::paFor_variable_declaration) {
      while (For_variable_declaration) {
        VectorOfany* stmts = for_stmt->VpiForInitStmts();
        if (stmts == nullptr) {
          for_stmt->VpiForInitStmts(s.MakeAnyVec());
          stmts = for_stmt->VpiForInitStmts();
        }

        NodeId Data_type = fC->Child(For_variable_declaration);
        NodeId Var = fC->Sibling(Data_type);
        NodeId Expression = fC->Sibling(Var);
        assignment* assign_stmt = s.MakeAssignment();
        assign_stmt->VpiParent(for_stmt);
        fC->populateCoreMembers(For_variable_declaration,
                                For_variable_declaration, assign_stmt);

        variables* var = (variables*)compileVariable(
            component, fC, Data_type, compileDesign, Reduce::Yes, assign_stmt,
            nullptr, false);
        if (var) {
          assign_stmt->Lhs(var);
          var->VpiParent(assign_stmt);
          var->VpiName(fC->SymName(Var));
          fC->populateCoreMembers(Var, Var, var);
        }

        expr* rhs = (expr*)compileExpression(component, fC, Expression,
                                             compileDesign, Reduce::No);
        if (rhs) {
          rhs->VpiParent(assign_stmt);
          assign_stmt->Rhs(rhs);
        }
        stmts->push_back(assign_stmt);

        For_variable_declaration = fC->Sibling(For_variable_declaration);
      }
    } else if (fC->Type(For_variable_declaration) ==
               VObjectType::paList_of_variable_assignments) {
      NodeId List_of_variable_assignments = For_variable_declaration;
      NodeId Variable_assignment = fC->Child(List_of_variable_assignments);
      while (Variable_assignment) {
        NodeId Variable_lvalue = fC->Child(Variable_assignment);
        NodeId Hierarchical_identifier = fC->Child(Variable_lvalue);
        if (fC->Type(fC->Child(Hierarchical_identifier)) ==
            VObjectType::paHierarchical_identifier) {
          Hierarchical_identifier =
              fC->Child(fC->Child(Hierarchical_identifier));
        } else if (fC->Type(Hierarchical_identifier) !=
                   VObjectType::paPs_or_hierarchical_identifier) {
          Hierarchical_identifier = Variable_lvalue;
        }
        NodeId Expression = fC->Sibling(Variable_lvalue);
        VectorOfany* stmts = for_stmt->VpiForInitStmts();
        if (stmts == nullptr) {
          for_stmt->VpiForInitStmts(s.MakeAnyVec());
          stmts = for_stmt->VpiForInitStmts();
        }

        assignment* assign_stmt = s.MakeAssignment();
        assign_stmt->VpiParent(for_stmt);
        fC->populateCoreMembers(Variable_assignment, Variable_assignment,
                                assign_stmt);

        variables* var = (variables*)compileVariable(
            component, fC, Hierarchical_identifier, compileDesign, Reduce::Yes,
            assign_stmt, nullptr, false);
        if (var) {
          assign_stmt->Lhs(var);
          var->VpiParent(assign_stmt);
        }

        expr* rhs = (expr*)compileExpression(component, fC, Expression,
                                             compileDesign, Reduce::No);
        if (rhs) rhs->VpiParent(assign_stmt);
        assign_stmt->Rhs(rhs);
        stmts->push_back(assign_stmt);

        Variable_assignment = fC->Sibling(Variable_assignment);
      }
    }
  }

  // Condition
  if (Condition) {
    expr* cond = (expr*)compileExpression(component, fC, Condition,
                                          compileDesign, Reduce::No);
    if (cond) {
      cond->VpiParent(for_stmt);
      for_stmt->VpiCondition(cond);
    }
  }

  // Increment
  if (For_step) {
    NodeId For_step_assignment = fC->Child(For_step);
    while (For_step_assignment) {
      VectorOfany* stmts = for_stmt->VpiForIncStmts();
      if (stmts == nullptr) {
        for_stmt->VpiForIncStmts(s.MakeAnyVec());
        stmts = for_stmt->VpiForIncStmts();
      }

      NodeId Expression = fC->Child(For_step_assignment);
      if (fC->Type(Expression) == VObjectType::paOperator_assignment) {
        std::vector<UHDM::any*>* incstmts = compileStmt(
            component, fC, Expression, compileDesign, Reduce::No, for_stmt);
        if (incstmts) {
          for (auto stmt : *incstmts) {
            stmts->push_back(stmt);
          }
        }
      } else {
        expr* exp = (expr*)compileExpression(component, fC, Expression,
                                             compileDesign, Reduce::No);
        if (exp) {
          exp->VpiParent(for_stmt);
          stmts->push_back(exp);
        }
      }
      For_step_assignment = fC->Sibling(For_step_assignment);
    }
  }

  // Stmt
  if (Statement_or_null) {
    VectorOfany* stmts =
        compileStmt(component, fC, Statement_or_null, compileDesign, Reduce::No,
                    for_stmt, nullptr, muteErrors);
    if (stmts) for_stmt->VpiStmt((*stmts)[0]);
  }

  /*
  n<> u<36> t<IntegerAtomType_Int> p<37> l<5>
  n<> u<37> t<Data_type> p<43> c<36> s<38> l<5>
  n<i> u<38> t<StringConst> p<43> s<42> l<5>
  n<PTR_WIDTH> u<39> t<StringConst> p<40> l<5>
  n<> u<40> t<Primary_literal> p<41> c<39> l<5>
  n<> u<41> t<Primary> p<42> c<40> l<5>
  n<> u<42> t<Expression> p<43> c<41> l<5>
  n<> u<43> t<For_variable_declaration> p<44> c<37> l<5>
  n<> u<44> t<For_initialization> p<84> c<43> s<54> l<5>
  n<i> u<45> t<StringConst> p<46> l<5>
  n<> u<46> t<Primary_literal> p<47> c<45> l<5>
  n<> u<47> t<Primary> p<48> c<46> l<5>
  n<> u<48> t<Expression> p<54> c<47> s<49> l<5>
  n<> u<49> t<BinOp_GreatEqual> p<54> s<53> l<5>
  n<0> u<50> t<IntConst> p<51> l<5>
  n<> u<51> t<Primary_literal> p<52> c<50> l<5>
  n<> u<52> t<Primary> p<53> c<51> l<5>
  n<> u<53> t<Expression> p<54> c<52> l<5>
  n<> u<54> t<Expression> p<84> c<48> s<63> l<5>
  n<i> u<55> t<StringConst> p<56> l<5>
  n<> u<56> t<Hierarchical_identifier> p<59> c<55> s<58> l<5>
  n<> u<57> t<Bit_select> p<58> l<5>
  n<> u<58> t<Select> p<59> c<57> l<5>
  n<> u<59> t<Variable_lvalue> p<61> c<56> s<60> l<5>
  n<> u<60> t<IncDec_MinusMinus> p<61> l<5>
  n<> u<61> t<Inc_or_dec_expression> p<62> c<59> l<5>
  n<> u<62> t<For_step_assignment> p<63> c<61> l<5>
  n<> u<63> t<For_step> p<84> c<62> s<82> l<5>
  n<dec_tmp> u<64> t<StringConst> p<65> l<6>
  n<> u<65> t<Hierarchical_identifier> p<72> c<64> s<71> l<6>
  n<i> u<66> t<StringConst> p<67> l<6>
  n<> u<67> t<Primary_literal> p<68> c<66> l<6>
  n<> u<68> t<Primary> p<69> c<67> l<6>
  n<> u<69> t<Expression> p<70> c<68> l<6>
  n<> u<70> t<Bit_select> p<71> c<69> l<6>
  n<> u<71> t<Select> p<72> c<70> l<6>
  n<> u<72> t<Variable_lvalue> p<78> c<65> s<73> l<6>
  n<> u<73> t<AssignOp_Assign> p<78> s<77> l<6>
  n<0> u<74> t<IntConst> p<75> l<6>
  n<> u<75> t<Primary_literal> p<76> c<74> l<6>
  n<> u<76> t<Primary> p<77> c<75> l<6>
  n<> u<77> t<Expression> p<78> c<76> l<6>
  n<> u<78> t<Operator_assignment> p<79> c<72> l<6>
  n<> u<79> t<Blocking_assignment> p<80> c<78> l<6>
  n<> u<80> t<Statement_item> p<81> c<79> l<6>
  n<> u<81> t<Statement> p<82> c<80> l<6>
  n<> u<82> t<Statement_or_null> p<84> c<81> l<6>
  n<> u<83> t<For> p<84> s<44> l<5>
  */

  return for_stmt;
}

UHDM::any* CompileHelper::bindParameter(DesignComponent* component,
                                        ValuedComponentI* instance,
                                        std::string_view name,
                                        CompileDesign* compileDesign,
                                        bool crossHierarchy) {
  if (instance) {
    ModuleInstance* inst = valuedcomponenti_cast<ModuleInstance*>(instance);
    while (inst) {
      if (Netlist* netlist = inst->getNetlist()) {
        if (netlist->param_assigns()) {
          for (param_assign* pass : *netlist->param_assigns()) {
            if (pass->Lhs()->VpiName() == name) {
              return pass->Lhs();
            }
          }
        }
      }
      if (crossHierarchy) {
        inst = inst->getParent();
      } else {
        break;
      }
    }
  }
  return nullptr;
}

UHDM::any* CompileHelper::bindVariable(DesignComponent* component,
                                       ValuedComponentI* instance,
                                       std::string_view name,
                                       CompileDesign* compileDesign) {
  UHDM::any* result = nullptr;
  if (ModuleInstance* inst = valuedcomponenti_cast<ModuleInstance*>(instance)) {
    Netlist* netlist = inst->getNetlist();
    if (netlist) {
      if (std::vector<UHDM::net*>* nets = netlist->nets()) {
        for (auto net : *nets) {
          if (net->VpiName() == name) {
            return net;
          }
        }
      }
      if (std::vector<UHDM::variables*>* vars = netlist->variables()) {
        for (auto var : *vars) {
          if (var->VpiName() == name) {
            return var;
          }
        }
      }
    }
  }
  return result;
}

UHDM::any* CompileHelper::bindVariable(DesignComponent* component,
                                       const UHDM::any* scope,
                                       std::string_view name,
                                       CompileDesign* compileDesign) {
  if (scope == nullptr) return nullptr;
  UHDM_OBJECT_TYPE scope_type = scope->UhdmType();
  switch (scope_type) {
    case uhdmfunction: {
      function* lscope = (function*)scope;
      if (lscope->Variables()) {
        for (auto var : *lscope->Variables()) {
          if (var->VpiName() == name) return var;
        }
      }
      if (lscope->Io_decls()) {
        for (auto var : *lscope->Io_decls()) {
          if (var->VpiName() == name) return var;
        }
      }
      break;
    }
    case uhdmtask: {
      task* lscope = (task*)scope;
      if (lscope->Variables()) {
        for (auto var : *lscope->Variables()) {
          if (var->VpiName() == name) return var;
        }
      }
      if (lscope->Io_decls()) {
        for (auto var : *lscope->Io_decls()) {
          if (var->VpiName() == name) return var;
        }
      }
      break;
    }
    case uhdmbegin: {
      begin* lscope = (begin*)scope;
      if (lscope->Variables()) {
        for (auto var : *lscope->Variables()) {
          if (var->VpiName() == name) return var;
        }
      }
      break;
    }
    case uhdmmodule_inst: {
      module_inst* mod = (module_inst*)scope;
      if (mod->Variables()) {
        for (auto var : *mod->Variables()) {
          if (var->VpiName() == name) return var;
        }
      }
      if (mod->Nets()) {
        for (auto var : *mod->Nets()) {
          if (var->VpiName() == name) return var;
        }
      }
      break;
    }
    default:
      break;
  }
  return bindVariable(component, scope->VpiParent(), name, compileDesign);
}

UHDM::method_func_call* CompileHelper::compileRandomizeCall(
    DesignComponent* component, const FileContent* fC, NodeId Identifier_list,
    CompileDesign* compileDesign, UHDM::any* pexpr) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  method_func_call* func_call = s.MakeMethod_func_call();
  method_func_call* result = func_call;
  func_call->VpiName("randomize");
  NodeId With;
  if (fC->Type(Identifier_list) == VObjectType::paIdentifier_list) {
    With = fC->Sibling(Identifier_list);
  } else if (fC->Type(Identifier_list) == VObjectType::paWITH) {
    With = Identifier_list;
  }
  NodeId Constraint_block = fC->Sibling(With);
  if (fC->Type(Identifier_list) == VObjectType::paIdentifier_list) {
    VectorOfany* arguments =
        compileTfCallArguments(component, fC, Identifier_list, compileDesign,
                               Reduce::No, func_call, nullptr, false);
    func_call->Tf_call_args(arguments);
  }

  if (Constraint_block) {
    if (UHDM::any* cblock = compileConstraintBlock(
            component, fC, Constraint_block, compileDesign, pexpr)) {
      func_call->With(cblock);
    }
  }
  return result;
}

UHDM::any* CompileHelper::compileConstraintBlock(DesignComponent* component,
                                                 const FileContent* fC,
                                                 NodeId nodeId,
                                                 CompileDesign* compileDesign,
                                                 UHDM::any* pexpr) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::any* result = nullptr;
  UHDM::constraint* cons = s.MakeConstraint();
  cons->VpiParent(pexpr);
  result = cons;
  return result;
}

void CompileHelper::compileBindStmt(DesignComponent* component,
                                    const FileContent* fC,
                                    NodeId Bind_directive,
                                    CompileDesign* compileDesign,
                                    ValuedComponentI* instance) {
  /*
  n<bp_lce> u<46> t<StringConst> p<65> s<64> l<9:5> el<9:11>
  n<bp_me_nonsynth_lce_tracer> u<47> t<StringConst> p<63> s<57> l<10:12>
  el<10:37> n<sets_p> u<48> t<StringConst> p<55> s<54> l<11:17> el<11:23>
  n<sets_p> u<49> t<StringConst> p<50> l<11:24> el<11:30>
  n<> u<50> t<Primary_literal> p<51> c<49> l<11:24> el<11:30>
  n<> u<51> t<Primary> p<52> c<50> l<11:24> el<11:30>
  n<> u<52> t<Expression> p<53> c<51> l<11:24> el<11:30>
  n<> u<53> t<Mintypmax_expression> p<54> c<52> l<11:24> el<11:30>
  n<> u<54> t<Param_expression> p<55> c<53> l<11:24> el<11:30>
  n<> u<55> t<Named_parameter_assignment> p<56> c<48> l<11:16> el<11:31>
  n<> u<56> t<List_of_parameter_assignments> p<57> c<55> l<11:16> el<11:31>
  n<> u<57> t<Parameter_value_assignment> p<63> c<56> s<62> l<11:14> el<11:32>
  n<lce_tracer1> u<58> t<StringConst> p<59> l<12:14> el<12:25>
  n<> u<59> t<Name_of_instance> p<62> c<58> s<61> l<12:14> el<12:25>
  n<> u<60> t<Ordered_port_connection> p<61> l<12:26> el<12:26>
  n<> u<61> t<List_of_port_connections> p<62> c<60> l<12:26> el<12:26>
  n<> u<62> t<Hierarchical_instance> p<63> c<59> l<12:14> el<12:27>
  n<> u<63> t<Module_instantiation> p<64> c<47> l<10:12> el<12:28>
  n<> u<64> t<Bind_instantiation> p<65> c<63> l<10:12> el<12:28>
  n<> u<65> t<Bind_directive> p<66> c<46> l<9:0> el<12:28>
  */
  /*
    bind_directive:
    bind bind_target_scope [ : bind_target_instance_list ] bind_instantiation ;
  | bind bind_target_instance bind_instantiation ;
  */
  NodeId Target_scope = fC->Child(Bind_directive);
  const std::string_view targetName = fC->SymName(Target_scope);
  NodeId Bind_instantiation = fC->Sibling(Target_scope);
  NodeId Instance_target;
  if (fC->Type(Bind_instantiation) == VObjectType::slStringConst) {
    Instance_target = Bind_instantiation;
    NodeId Constant_bit_select = fC->Sibling(Bind_instantiation);
    Bind_instantiation = fC->Sibling(Constant_bit_select);
  }
  NodeId Module_instantiation = fC->Child(Bind_instantiation);
  NodeId Source_scope = fC->Child(Module_instantiation);
  NodeId tmp = fC->Sibling(Source_scope);
  if (fC->Type(tmp) == VObjectType::paParameter_value_assignment) {
    tmp = fC->Sibling(tmp);
  }
  NodeId Instance_name = tmp;
  Instance_name = fC->Child(fC->Child(Instance_name));
  std::string fullName = StrCat(fC->getLibrary()->getName(), "@", targetName);
  BindStmt* bind = new BindStmt(fC, Module_instantiation, Target_scope,
                                Instance_target, Source_scope, Instance_name);
  compileDesign->getCompiler()->getDesign()->addBindStmt(fullName, bind);
}

UHDM::any* CompileHelper::compileCheckerInstantiation(
    DesignComponent* component, const FileContent* fC, NodeId nodeId,
    CompileDesign* compileDesign, UHDM::any* pstmt,
    ValuedComponentI* instance) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::checker_inst* result = s.MakeChecker_inst();
  NodeId Ps_identifier = fC->Child(nodeId);
  const std::string_view CheckerName = fC->SymName(Ps_identifier);
  result->VpiDefName(CheckerName);
  NodeId Name_of_instance = fC->Sibling(nodeId);
  NodeId InstanceName = fC->Child(Name_of_instance);
  const std::string_view InstName = fC->SymName(InstanceName);
  result->VpiName(InstName);
  return result;
}

}  // namespace SURELOG
