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

#include "Surelog/Common/PathId.h"
#include "Surelog/Design/DesignComponent.h"
#include "Surelog/Design/ParamAssign.h"
#include "Surelog/DesignCompile/CompileDesign.h"
#include "Surelog/DesignCompile/CompileHelper.h"
#include "Surelog/Expression/Value.h"
#include "Surelog/SourceCompile/Compiler.h"
#include "Surelog/SourceCompile/SymbolTable.h"
#include "Surelog/Utils/StringUtils.h"

// UHDM
#include <uhdm/ElaboratorListener.h>
#include <uhdm/ExprEval.h>
#include <uhdm/clone_tree.h>
#include <uhdm/expr.h>
#include <uhdm/uhdm.h>
#include <uhdm/uhdm_types.h>

#include <bitset>
#include <cstdint>
#include <iostream>
#include <string>
#include <string_view>
#include <vector>

namespace SURELOG {

uhdm::Expr* CompileHelper::EvalFunc(uhdm::Function* func,
                                    std::vector<uhdm::Any*>* args,
                                    bool& invalidValue,
                                    DesignComponent* component,
                                    CompileDesign* compileDesign,
                                    ValuedComponentI* instance, PathId fileId,
                                    uint32_t lineNumber, uhdm::Any* pexpr) {
  if (m_reduce == Reduce::Yes) {
    invalidValue = true;
    return nullptr;
  }

  uhdm::GetObjectFunctor getObjectFunctor =
      [&](std::string_view name, const uhdm::Any* inst,
          const uhdm::Any* pexpr) -> uhdm::Any* {
    return getObject(name, component, compileDesign, instance, pexpr);
  };
  uhdm::GetObjectFunctor getValueFunctor =
      [&](std::string_view name, const uhdm::Any* inst,
          const uhdm::Any* pexpr) -> uhdm::Any* {
    return (uhdm::Expr*)getValue(name, component, compileDesign, Reduce::Yes,
                                 instance, fileId, lineNumber,
                                 (uhdm::Any*)pexpr, false);
  };
  uhdm::GetTaskFuncFunctor getTaskFuncFunctor =
      [&](std::string_view name, const uhdm::Any* inst) -> uhdm::TaskFunc* {
    auto ret = getTaskFunc(name, component, compileDesign, instance, pexpr);
    return ret.first;
  };
  uhdm::ExprEval eval;
  eval.setGetObjectFunctor(getObjectFunctor);
  eval.setGetValueFunctor(getValueFunctor);
  eval.setGetTaskFuncFunctor(getTaskFuncFunctor);
  if (m_exprEvalPlaceHolder == nullptr) {
    m_exprEvalPlaceHolder = compileDesign->getSerializer().make<uhdm::Module>();
    m_exprEvalPlaceHolder->setParamAssigns(
        compileDesign->getSerializer().makeCollection<uhdm::ParamAssign>());
  } else {
    m_exprEvalPlaceHolder->getParamAssigns()->erase(
        m_exprEvalPlaceHolder->getParamAssigns()->begin(),
        m_exprEvalPlaceHolder->getParamAssigns()->end());
  }
  uhdm::Expr* res =
      eval.evalFunc(func, args, invalidValue, m_exprEvalPlaceHolder, pexpr);
  return res;
}

void CompileHelper::evalScheduledExprs(DesignComponent* component,
                                       CompileDesign* compileDesign) {
  for (auto& nameEval : component->getScheduledParamExprEval()) {
    const std::string& name = nameEval.first;
    ExprEval& expr_eval = nameEval.second;
    bool invalidValue = false;
    uhdm::Expr* result =
        reduceExpr(expr_eval.m_expr, invalidValue, component, compileDesign,
                   expr_eval.m_instance, expr_eval.m_fileId,
                   expr_eval.m_lineNumber, expr_eval.m_pexpr);
    if (!invalidValue && result &&
        (result->getUhdmType() == uhdm::UhdmType::Constant)) {
      uhdm::Constant* c = (uhdm::Constant*)result;
      Value* val = m_exprBuilder.fromVpiValue(c->getValue(), c->getSize());
      component->setValue(name, val, m_exprBuilder);
      for (ParamAssign* pass : component->getParamAssignVec()) {
        if (uhdm::ParamAssign* upass = pass->getUhdmParamAssign()) {
          if (upass->getLhs()->getName() == name) {
            upass->setRhs(result);
            break;
          }
        }
      }
    }
  }
}
}  // namespace SURELOG
