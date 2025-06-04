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

#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Design/DataType.h"
#include "Surelog/Design/DummyType.h"
#include "Surelog/Design/Enum.h"
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
#include "Surelog/DesignCompile/CompileDesign.h"
#include "Surelog/DesignCompile/CompileHelper.h"
#include "Surelog/DesignCompile/UhdmWriter.h"
#include "Surelog/ErrorReporting/Error.h"
#include "Surelog/ErrorReporting/ErrorContainer.h"
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
#include <string.h>
#include <uhdm/ElaboratorListener.h>
#include <uhdm/ExprEval.h>
#include <uhdm/VpiListener.h>
#include <uhdm/clone_tree.h>
#include <uhdm/expr.h>
#include <uhdm/uhdm.h>

#include <climits>
#include <iostream>
#include <string>
#include <vector>

namespace SURELOG {

using namespace uhdm;  // NOLINT (we use a good chunk of these here)

uhdm::AnyCollection* CompileHelper::compileGenVars(
    DesignComponent* component, const FileContent* fC, NodeId id,
    CompileDesign* compileDesign) {
  Serializer& s = compileDesign->getSerializer();
  AnyCollection* vars = nullptr;
  NodeId identifierListId = fC->Child(id);
  while (identifierListId) {
    NodeId nameId = fC->Child(identifierListId);

    uhdm::GenVar* var = s.make<uhdm::GenVar>();
    var->setName(fC->SymName(nameId));
    fC->populateCoreMembers(nameId, nameId, var);

    if (vars == nullptr) vars = s.makeCollection<Any>();
    vars->emplace_back(var);

    identifierListId = fC->Sibling(identifierListId);
  }
  return vars;
}

uhdm::AnyCollection* CompileHelper::compileGenStmt(
    DesignComponent* component, const FileContent* fC, NodeId id,
    CompileDesign* compileDesign) {
  Serializer& s = compileDesign->getSerializer();
  NodeId stmtId = fC->Child(id);
  uhdm::Any* genstmt = nullptr;
  if (fC->Type(id) == VObjectType::paGenerate_region) {
    uhdm::GenRegion* genreg = s.make<uhdm::GenRegion>();
    fC->populateCoreMembers(id, id, genreg);
    genstmt = genreg;
    const uhdm::ScopedScope scopedScope1(genreg);

    uhdm::Begin* stmt = s.make<uhdm::Begin>();
    stmt->setParent(genreg);
    fC->populateCoreMembers(stmtId, stmtId, stmt);
    genreg->setStmt(stmt);

    checkForLoops(true);
    const uhdm::ScopedScope scopedScope2(stmt);
    if (uhdm::AnyCollection* stmts =
            compileStmt(component, fC, stmtId, compileDesign, Reduce::No, stmt,
                        nullptr, true)) {
      stmt->setStmts(stmts);
    }
    checkForLoops(false);

    NodeId blockNameId = fC->Child(fC->Child(stmtId));
    if (fC->Type(blockNameId) == VObjectType::slStringConst) {
      stmt->setName(fC->SymName(blockNameId));
    }
  } else if (fC->Type(stmtId) ==
             VObjectType::paIf_generate_construct) {  // If, If-Else stmt
    NodeId ifElseId = fC->Child(stmtId);
    if (fC->Type(ifElseId) == VObjectType::paIF) {
      // lookahead
      NodeId tmp = ifElseId;
      bool ifelse = false;
      while (tmp) {
        if (fC->Type(tmp) == VObjectType::paELSE) {
          ifelse = true;
          break;
        }
        tmp = fC->Sibling(tmp);
      }

      NodeId condId = fC->Sibling(ifElseId);
      checkForLoops(true);
      uhdm::Expr* cond = (uhdm::Expr*)compileExpression(
          component, fC, condId, compileDesign, Reduce::No, nullptr);
      checkForLoops(false);

      NodeId stmtId = fC->Sibling(condId);
      if (ifelse) {
        uhdm::GenIfElse* genif = s.make<uhdm::GenIfElse>();
        genstmt = genif;
        if (cond != nullptr) {
          cond->setParent(genif, true);
          genif->setCondition(cond);
        }

        uhdm::Begin* stmt1 = s.make<uhdm::Begin>();
        fC->populateCoreMembers(stmtId, stmtId, stmt1);
        stmt1->setParent(genif);
        genif->setStmt(stmt1);

        checkForLoops(true);
        {
          const uhdm::ScopedScope scopedScope1(stmt1);
          if (uhdm::AnyCollection* stmts =
                  compileStmt(component, fC, stmtId, compileDesign, Reduce::No,
                              stmt1, nullptr, true)) {
            stmt1->setStmts(stmts);
          }
        }
        checkForLoops(false);

        NodeId blockNameId = fC->Child(fC->Child(stmtId));
        if (fC->Type(blockNameId) == VObjectType::slStringConst) {
          stmt1->setName(fC->SymName(blockNameId));
        }

        NodeId ElseId = fC->Sibling(stmtId);
        NodeId elseStmtId = fC->Sibling(ElseId);

        uhdm::Begin* stmt2 = s.make<uhdm::Begin>();
        fC->populateCoreMembers(elseStmtId, elseStmtId, stmt2);
        stmt2->setParent(genif);
        genif->setElseStmt(stmt2);

        checkForLoops(true);
        {
          const uhdm::ScopedScope scopedScope2(stmt2);
          if (uhdm::AnyCollection* stmts =
                  compileStmt(component, fC, elseStmtId, compileDesign,
                              Reduce::No, stmt2, nullptr, true)) {
            stmt2->setStmts(stmts);
          }
        }
        checkForLoops(false);

        blockNameId = fC->Child(fC->Child(elseStmtId));
        if (fC->Type(blockNameId) == VObjectType::slStringConst) {
          stmt2->setName(fC->SymName(blockNameId));
        }
        fC->populateCoreMembers(ifElseId, elseStmtId, genif);
      } else {
        uhdm::GenIf* genif = s.make<uhdm::GenIf>();
        genstmt = genif;
        if (cond != nullptr) {
          cond->setParent(genif, true);
          genif->setCondition(cond);
        }
        fC->populateCoreMembers(id, id, genif);

        uhdm::Begin* stmt = s.make<uhdm::Begin>();
        fC->populateCoreMembers(stmtId, stmtId, stmt);
        stmt->setParent(genif);
        genif->setStmt(stmt);

        checkForLoops(true);
        const uhdm::ScopedScope scopedScope(stmt);
        if (uhdm::AnyCollection* stmts =
                compileStmt(component, fC, stmtId, compileDesign, Reduce::No,
                            stmt, nullptr, true)) {
          stmt->setStmts(stmts);
        }
        checkForLoops(false);

        NodeId blockNameId = fC->Child(fC->Child(stmtId));
        if (fC->Type(blockNameId) == VObjectType::slStringConst) {
          stmt->setName(fC->SymName(blockNameId));
        }
      }
    }
  } else if (fC->Type(stmtId) ==
             VObjectType::paCase_generate_construct) {  // Case
    NodeId tmp = fC->Child(stmtId);
    uhdm::GenCase* gencase = s.make<uhdm::GenCase>();
    fC->populateCoreMembers(stmtId, stmtId, gencase);
    genstmt = gencase;
    checkForLoops(true);
    if (uhdm::Expr* cond = (uhdm::Expr*)compileExpression(
            component, fC, tmp, compileDesign, Reduce::No, gencase)) {
      gencase->setCondition(cond);
    }
    checkForLoops(false);
    uhdm::CaseItemCollection* items = gencase->getCaseItems(true);
    tmp = fC->Sibling(tmp);
    while (tmp) {
      if (fC->Type(tmp) == VObjectType::paCase_generate_item) {
        uhdm::CaseItem* citem = s.make<uhdm::CaseItem>();
        citem->setParent(gencase);
        fC->populateCoreMembers(tmp, tmp, citem);
        items->emplace_back(citem);

        NodeId itemExp = fC->Child(tmp);
        NodeId stmtId = itemExp;
        if (fC->Type(itemExp) == VObjectType::paConstant_expression) {
          checkForLoops(true);
          if (uhdm::Expr* ex = (uhdm::Expr*)compileExpression(
                  component, fC, itemExp, compileDesign, Reduce::No, citem)) {
            citem->getExprs(true)->emplace_back(ex);
          }
          checkForLoops(false);
          stmtId = fC->Sibling(stmtId);
        }

        uhdm::Begin* stmt = s.make<uhdm::Begin>();
        stmt->setParent(citem);
        fC->populateCoreMembers(stmtId, stmtId, stmt);
        citem->setStmt(stmt);

        checkForLoops(true);
        const uhdm::ScopedScope scopedScope(stmt);
        if (uhdm::AnyCollection* stmts =
                compileStmt(component, fC, stmtId, compileDesign, Reduce::No,
                            stmt, nullptr, true)) {
          stmt->setStmts(stmts);
        }
        checkForLoops(false);

        NodeId blockNameId = fC->Child(fC->Child(stmtId));
        if (fC->Type(blockNameId) == VObjectType::slStringConst) {
          stmt->setName(fC->SymName(blockNameId));
        }
      }
      tmp = fC->Sibling(tmp);
    }
  } else if (fC->Type(stmtId) == VObjectType::paGenvar_initialization ||
             fC->Type(stmtId) ==
                 VObjectType::paGenvar_decl_assignment) {  // For loop stmt
    NodeId varInit = stmtId;
    NodeId endLoopTest = fC->Sibling(varInit);
    uhdm::GenFor* genfor = s.make<uhdm::GenFor>();
    fC->populateCoreMembers(id, id, genfor);
    genstmt = genfor;
    const uhdm::ScopedScope scopedScope1(genfor);

    // Var init
    NodeId Var = fC->Child(varInit);
    NodeId Expression = fC->Sibling(Var);
    uhdm::Assignment* assign_stmt = s.make<uhdm::Assignment>();
    assign_stmt->setParent(genfor);
    fC->populateCoreMembers(varInit, varInit, assign_stmt);
    if (uhdm::Variables* varb = (uhdm::Variables*)compileVariable(
            component, fC, Var, Var, compileDesign, Reduce::No, genfor, nullptr,
            false)) {
      assign_stmt->setLhs(varb);
      varb->setParent(assign_stmt);
      varb->setName(fC->SymName(Var));
      fC->populateCoreMembers(Var, Var, varb);
    }
    checkForLoops(true);
    if (uhdm::Expr* rhs = (uhdm::Expr*)compileExpression(
            component, fC, Expression, compileDesign, Reduce::No,
            assign_stmt)) {
      assign_stmt->setRhs(rhs);
    }
    checkForLoops(false);
    genfor->getForInitStmts(true)->emplace_back(assign_stmt);

    // Condition
    checkForLoops(true);
    if (uhdm::Expr* cond = (uhdm::Expr*)compileExpression(
            component, fC, endLoopTest, compileDesign, Reduce::No, genfor)) {
      genfor->setCondition(cond);
    }
    checkForLoops(false);

    // Iteration
    NodeId iteration = fC->Sibling(endLoopTest);
    NodeId var = fC->Child(iteration);
    NodeId assignOp = fC->Sibling(var);
    NodeId exprId = fC->Sibling(assignOp);
    if (!exprId) {  // Unary operator like i++
      exprId = iteration;
      checkForLoops(true);
      if (uhdm::Expr* ex = (uhdm::Expr*)compileExpression(
              component, fC, exprId, compileDesign, Reduce::No, genfor)) {
        genfor->setForIncStmt(ex);
      }
      checkForLoops(false);
    } else {
      uhdm::Assignment* assign_stmt = s.make<uhdm::Assignment>();
      assign_stmt->setOpType(UhdmWriter::getVpiOpType(fC->Type(assignOp)));
      genfor->setForIncStmt(assign_stmt);
      assign_stmt->setParent(genfor);
      fC->populateCoreMembers(iteration, iteration, assign_stmt);
      checkForLoops(true);
      if (uhdm::Expr* lhs = (uhdm::Expr*)compileExpression(
              component, fC, var, compileDesign, Reduce::No, assign_stmt)) {
        assign_stmt->setLhs(lhs);
      }
      if (uhdm::Expr* rhs = (uhdm::Expr*)compileExpression(
              component, fC, exprId, compileDesign, Reduce::No, assign_stmt)) {
        assign_stmt->setRhs(rhs);
      }
      checkForLoops(false);
    }

    // Stmts
    NodeId genBlock = fC->Sibling(iteration);

    uhdm::Begin* stmt = s.make<uhdm::Begin>();
    stmt->setParent(genfor);
    fC->populateCoreMembers(genBlock, genBlock, stmt);
    genfor->setStmt(stmt);

    checkForLoops(true);
    const uhdm::ScopedScope scopedScope2(stmt);
    if (uhdm::AnyCollection* stmts =
            compileStmt(component, fC, genBlock, compileDesign, Reduce::No,
                        stmt, nullptr, true)) {
      stmt->setStmts(stmts);
    }
    checkForLoops(false);

    NodeId blockNameId = fC->Child(fC->Child(genBlock));
    if (fC->Type(blockNameId) == VObjectType::slStringConst) {
      stmt->setName(fC->SymName(blockNameId));
    }
  }
  uhdm::AnyCollection* stmts = s.makeCollection<Any>();
  if (genstmt) stmts->emplace_back(genstmt);
  return stmts;
}

}  // namespace SURELOG
