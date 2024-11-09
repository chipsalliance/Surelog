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
 * File:   ElaborationStep.h
 * Author: alain
 *
 * Created on July 12, 2017, 8:55 PM
 */

#ifndef SURELOG_ELABORATIONSTEP_H
#define SURELOG_ELABORATIONSTEP_H
#pragma once

#include <string_view>
#include <Surelog/DesignCompile/CompileHelper.h>
#include <Surelog/ErrorReporting/ErrorDefinition.h>
#include <Surelog/Expression/ExprBuilder.h>

// UHDM
#include <uhdm/uhdm_forward_decl.h>

#include <string>
#include <vector>

namespace SURELOG {

class CompileDesign;
class ErrorContainer;
class ModuleInstance;
class Parameter;
class Scope;
class Signal;
class SymbolTable;
class TypeDef;
class Variable;

class ElaborationStep {
 public:
  explicit ElaborationStep(CompileDesign* compileDesign);
  ElaborationStep(const ElaborationStep& orig) = delete;

  virtual bool elaborate() = 0;

  virtual ~ElaborationStep();

 protected:
  bool bindTypedefs_();
  bool bindTypedefsPostElab_();

  const DataType* bindTypeDef_(TypeDef* typd, const DesignComponent* parent,
                               ErrorDefinition::ErrorType errtype);

  const DataType* bindDataType_(std::string_view type_name,
                                const FileContent* fC, NodeId id,
                                const DesignComponent* parent,
                                ErrorDefinition::ErrorType errtype);

  Variable* bindVariable_(std::string_view var_name, Scope* scope,
                          const FileContent* fc, NodeId id,
                          const DesignComponent* parent,
                          ErrorDefinition::ErrorType errtype,
                          bool returnClassParam);

  Variable* locateVariable_(const std::vector<std::string_view>& var_chain,
                            const FileContent* fC, NodeId id, Scope* scope,
                            DesignComponent* parentComponent,
                            ErrorDefinition::ErrorType errtype);

  Variable* locateStaticVariable_(
      const std::vector<std::string_view>& var_chain, const FileContent* fC,
      NodeId id, Scope* scope, DesignComponent* parentComponent,
      ErrorDefinition::ErrorType errtype);

  bool bindPortType_(Signal* port, const FileContent* fC, NodeId id,
                     Scope* scope, ModuleInstance* instance,
                     DesignComponent* parentComponent,
                     ErrorDefinition::ErrorType errtype);

  UHDM::expr* exprFromAssign_(DesignComponent* component, const FileContent* fC,
                              NodeId id, NodeId unpackedDimension,
                              ModuleInstance* instance);

  UHDM::typespec* elabTypeParameter_(DesignComponent* component,
                                     Parameter* typeParam,
                                     ModuleInstance* instance);

  UHDM::any* makeVar_(DesignComponent* component, Signal* sig,
                      std::vector<UHDM::range*>* packedDimensions,
                      int32_t packedSize,
                      std::vector<UHDM::range*>* unpackedDimensions,
                      int32_t unpackedSize, ModuleInstance* instance,
                      UHDM::VectorOfvariables* vars, UHDM::expr* assignExp,
                      UHDM::typespec* tps);

  void swapTypespecPointersInUhdm(UHDM::Serializer& s, std::map<const UHDM::typespec*, const UHDM::typespec*>& typespecSwapMap);
  void swapTypespecPointersInTypedef(Design* design, std::map<const UHDM::typespec*, const UHDM::typespec*>& typespecSwapMap);

  CompileDesign* m_compileDesign;
  ExprBuilder m_exprBuilder;
  SymbolTable* m_symbols;
  ErrorContainer* m_errors;
  CompileHelper m_helper;

  std::map<std::string, Variable*> m_staticVariables;
};

};  // namespace SURELOG

#endif /* SURELOG_ELABORATIONSTEP_H */
