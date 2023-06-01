/*
 Copyright 2019-2023 Alain Dargelas

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
 * File:   CompileGenStmt.cpp
 * Author: alain
 *
 * Created on May 14, 2023, 11:45 AM
 */

#include <Surelog/CommandLine/CommandLineParser.h>
#include <Surelog/Common/FileSystem.h>
#include <Surelog/Design/DataType.h>
#include <Surelog/Design/DummyType.h>
#include <Surelog/Design/Enum.h>
#include <Surelog/Design/FileContent.h>
#include <Surelog/Design/ModuleDefinition.h>
#include <Surelog/Design/ModuleInstance.h>
#include <Surelog/Design/Netlist.h>
#include <Surelog/Design/ParamAssign.h>
#include <Surelog/Design/Parameter.h>
#include <Surelog/Design/Signal.h>
#include <Surelog/Design/SimpleType.h>
#include <Surelog/Design/Struct.h>
#include <Surelog/Design/TfPortItem.h>
#include <Surelog/Design/Union.h>
#include <Surelog/DesignCompile/CompileDesign.h>
#include <Surelog/DesignCompile/CompileHelper.h>
#include <Surelog/DesignCompile/UhdmWriter.h>
#include <Surelog/ErrorReporting/Error.h>
#include <Surelog/ErrorReporting/ErrorContainer.h>
#include <Surelog/ErrorReporting/Location.h>
#include <Surelog/Library/Library.h>
#include <Surelog/Package/Package.h>
#include <Surelog/SourceCompile/Compiler.h>
#include <Surelog/SourceCompile/SymbolTable.h>
#include <Surelog/Testbench/ClassDefinition.h>
#include <Surelog/Testbench/Program.h>
#include <Surelog/Testbench/TypeDef.h>
#include <Surelog/Testbench/Variable.h>
#include <Surelog/Utils/NumUtils.h>
#include <Surelog/Utils/StringUtils.h>

// UHDM
#include <string.h>
#include <uhdm/ElaboratorListener.h>
#include <uhdm/ExprEval.h>
#include <uhdm/VpiListener.h>
#include <uhdm/clone_tree.h>
#include <uhdm/uhdm.h>

#include <climits>
#include <iostream>
#include <string>
#include <vector>

namespace SURELOG {

using namespace UHDM;  // NOLINT (we use a good chunk of these here)

void CompileHelper::compileGenStmt(ModuleDefinition* component,
                                   const FileContent* fC,
                                   CompileDesign* compileDesign, NodeId id) {
  Serializer& s = compileDesign->getSerializer();
  NodeId stmtId = fC->Child(id);
  gen_stmt* genstmt = nullptr;
  if (fC->Type(stmtId) ==
      VObjectType::slIf_generate_construct) {  // If, If-Else stmt
    NodeId ifElseId = fC->Child(stmtId);
    if (fC->Type(ifElseId) == VObjectType::slIF) {
      // lookahead
      NodeId tmp = ifElseId;
      bool ifelse = false;
      while (tmp) {
        if (fC->Type(tmp) == VObjectType::slElse) {
          ifelse = true;
          break;
        }
        tmp = fC->Sibling(tmp);
      }

      NodeId condId = fC->Sibling(ifElseId);
      expr* cond = (expr*)compileExpression(component, fC, condId,
                                            compileDesign, Reduce::No, nullptr);
      NodeId stmtId = fC->Sibling(condId);
      if (ifelse) {
        gen_if_else* genif = s.MakeGen_if_else();
        genstmt = genif;
        genif->VpiCondition(cond);
        begin* stmt = s.MakeBegin();
        VectorOfany* stmts = compileStmt(component, fC, stmtId, compileDesign,
                                         Reduce::No, nullptr, nullptr, true);
        stmt->Stmts(stmts);
        genif->VpiStmt(stmt);
        NodeId ElseId = fC->Sibling(stmtId);
        NodeId elseStmtId = fC->Sibling(ElseId);
        stmts = compileStmt(component, fC, elseStmtId, compileDesign,
                            Reduce::No, nullptr, nullptr, true);
        stmt = s.MakeBegin();
        stmt->Stmts(stmts);
        genif->VpiElseStmt(stmt);
      } else {
        gen_if* genif = s.MakeGen_if();
        genstmt = genif;
        genif->VpiCondition(cond);
        fC->populateCoreMembers(ifElseId, ifElseId, genif);
        begin* stmt = s.MakeBegin();
        VectorOfany* stmts = compileStmt(component, fC, stmtId, compileDesign,
                                         Reduce::No, nullptr, nullptr, true);
        stmt->Stmts(stmts);
        genif->VpiStmt(stmt);
      }
    }
  } else if (fC->Type(stmtId) == VObjectType::slGenvar_initialization ||
             fC->Type(stmtId) ==
                 VObjectType::slGenvar_decl_assignment) {  // For loop stmt

    NodeId varInit = stmtId;
    NodeId endLoopTest = fC->Sibling(varInit);
    gen_for* genfor = s.MakeGen_for();
    genstmt = genfor;

    // Var init
    genfor->VpiForInitStmts(s.MakeAnyVec());
    VectorOfany* stmts = genfor->VpiForInitStmts();

    NodeId Var = fC->Child(varInit);
    NodeId Expression = fC->Sibling(Var);
    assign_stmt* assign_stmt = s.MakeAssign_stmt();
    assign_stmt->VpiParent(genfor);
    fC->populateCoreMembers(varInit, varInit, assign_stmt);
    variables* varb =
        (variables*)compileVariable(component, fC, Var, compileDesign,
                                    Reduce::No, assign_stmt, nullptr, false);
    if (varb) {
      assign_stmt->Lhs(varb);
      varb->VpiParent(assign_stmt);
      varb->VpiName(fC->SymName(Var));
      fC->populateCoreMembers(Var, Var, varb);
    }
    expr* rhs = (expr*)compileExpression(component, fC, Expression,
                                         compileDesign, Reduce::No);
    if (rhs) {
      rhs->VpiParent(assign_stmt);
      assign_stmt->Rhs(rhs);
    }
    stmts->push_back(assign_stmt);

    // Condition
    expr* cond = (expr*)compileExpression(component, fC, endLoopTest,
                                          compileDesign, Reduce::No);
    genfor->VpiCondition(cond);

    // Iteration
    NodeId iteration = fC->Sibling(endLoopTest);
    NodeId var = fC->Child(iteration);
    NodeId assignOp = fC->Sibling(var);
    NodeId exprId = fC->Sibling(assignOp);
    if (!exprId) {  // Unary operator like i++
      exprId = iteration;
      expr* ex = (expr*)compileExpression(component, fC, exprId, compileDesign,
                                          Reduce::No);
      genfor->VpiForIncStmt(ex);
    } else {
      assignment* assign_stmt = s.MakeAssignment();
      assign_stmt->VpiOpType(UhdmWriter::getVpiOpType(fC->Type(assignOp)));
      genfor->VpiForIncStmt(assign_stmt);
      assign_stmt->VpiParent(genfor);
      fC->populateCoreMembers(iteration, iteration, assign_stmt);
      expr* lhs = (expr*)compileExpression(component, fC, var, compileDesign,
                                           Reduce::No);
      assign_stmt->Lhs(lhs);
      expr* rhs = (expr*)compileExpression(component, fC, exprId, compileDesign,
                                           Reduce::No);
      assign_stmt->Rhs(rhs);
    }

    // Stmts
    NodeId genBlock = fC->Sibling(iteration);
    begin* stmt = s.MakeBegin();
    stmts = compileStmt(component, fC, genBlock, compileDesign, Reduce::No,
                        nullptr, nullptr, true);
    stmt->Stmts(stmts);
    genfor->VpiStmt(stmt);
  }
  if (component->getGenStmts() == nullptr) {
    component->setGenStmts(s.MakeGen_stmtVec());
  }
  if (genstmt) component->getGenStmts()->push_back(genstmt);
}

}  // namespace SURELOG