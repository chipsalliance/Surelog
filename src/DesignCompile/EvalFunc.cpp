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

#include <Surelog/Design/DesignComponent.h>
#include <Surelog/Design/ParamAssign.h>
#include <Surelog/DesignCompile/CompileDesign.h>
#include <Surelog/DesignCompile/CompileHelper.h>
#include <Surelog/SourceCompile/Compiler.h>
#include <Surelog/SourceCompile/SymbolTable.h>
#include <Surelog/Utils/FileUtils.h>
#include <Surelog/Utils/StringUtils.h>

// UHDM
#include <uhdm/ElaboratorListener.h>
#include <uhdm/ExprEval.h>
#include <uhdm/clone_tree.h>
#include <uhdm/uhdm.h>

#include <bitset>
#include <iostream>

namespace SURELOG {

namespace fs = std::filesystem;
using namespace UHDM;  // NOLINT (using a bunch of them)

expr* CompileHelper::EvalFunc(UHDM::function* func, std::vector<any*>* args,
                              bool& invalidValue, DesignComponent* component,
                              CompileDesign* compileDesign,
                              ValuedComponentI* instance,
                              const fs::path& fileName, int lineNumber,
                              any* pexpr) {
  UHDM::GetObjectFunctor getObjectFunctor =
      [&](const std::string& name, const any* inst,
          const any* pexpr) -> UHDM::any* {
    return getObject(name, component, compileDesign, instance, pexpr);
  };
  UHDM::GetObjectFunctor getValueFunctor = [&](const std::string& name,
                                               const any* inst,
                                               const any* pexpr) -> UHDM::any* {
    return (expr*)getValue(name, component, compileDesign, instance, fileName,
                           lineNumber, (any*)pexpr, true, false);
  };
  UHDM::GetTaskFuncFunctor getTaskFuncFunctor =
      [&](const std::string& name, const any* inst) -> UHDM::task_func* {
    auto ret = getTaskFunc(name, component, compileDesign, instance, pexpr);
    return ret.first;
  };
  UHDM::ExprEval eval;
  eval.setGetObjectFunctor(getObjectFunctor);
  eval.setGetValueFunctor(getValueFunctor);
  eval.setGetTaskFuncFunctor(getTaskFuncFunctor);
  if (m_exprEvalPlaceHolder == nullptr) {
    m_exprEvalPlaceHolder = compileDesign->getSerializer().MakeModule();
    m_exprEvalPlaceHolder->Param_assigns(
        compileDesign->getSerializer().MakeParam_assignVec());
  } else {
    m_exprEvalPlaceHolder->Param_assigns()->erase(
        m_exprEvalPlaceHolder->Param_assigns()->begin(),
        m_exprEvalPlaceHolder->Param_assigns()->end());
  }
  expr* res = eval.EvalFunc(func, args, invalidValue, m_exprEvalPlaceHolder,
                            fileName, lineNumber, pexpr);
  return res;
}

void CompileHelper::evalScheduledExprs(DesignComponent* component,
                                       CompileDesign* compileDesign) {
  for (auto& nameEval : component->getScheduledParamExprEval()) {
    const std::string& name = nameEval.first;
    ExprEval& expr_eval = nameEval.second;
    bool invalidValue = false;
    expr* result =
        reduceExpr(expr_eval.m_expr, invalidValue, component, compileDesign,
                   expr_eval.m_instance, expr_eval.m_fileName,
                   expr_eval.m_lineNumber, expr_eval.m_pexpr);
    if (result && result->UhdmType() == uhdmconstant) {
      UHDM::constant* c = (UHDM::constant*)result;
      Value* val = m_exprBuilder.fromVpiValue(c->VpiValue(), c->VpiSize());
      component->setValue(name, val, m_exprBuilder);
      for (ParamAssign* pass : component->getParamAssignVec()) {
        if (param_assign* upass = pass->getUhdmParamAssign()) {
          if (upass->Lhs()->VpiName() == name) {
            upass->Rhs(result);
            break;
          }
        }
      }
    }
  }
}
}  // namespace SURELOG
