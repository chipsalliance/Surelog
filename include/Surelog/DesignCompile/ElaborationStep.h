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

#include <Surelog/DesignCompile/CompileHelper.h>
#include <Surelog/ErrorReporting/ErrorDefinition.h>
#include <Surelog/Expression/ExprBuilder.h>

#include <cstdint>
#include <map>
#include <string>
#include <string_view>
#include <vector>

// UHDM
#include <uhdm/Serializer.h>
#include <uhdm/containers.h>
#include <uhdm/uhdm_forward_decl.h>

namespace SURELOG {
class CompileDesign;
class ModuleInstance;
class Parameter;
class Scope;
class Session;
class Signal;
class TypeDef;
class Variable;

class ElaborationStep {
 public:
  ElaborationStep(Session* session, CompileDesign* compileDesign);
  ElaborationStep(const ElaborationStep& orig) = delete;
  virtual ~ElaborationStep() = default;

  virtual bool elaborate() = 0;

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

  uhdm::Expr* exprFromAssign_(DesignComponent* component, const FileContent* fC,
                              NodeId id, NodeId unpackedDimension,
                              ModuleInstance* instance);

  uhdm::Typespec* elabTypeParameter_(DesignComponent* component,
                                     Parameter* typeParam,
                                     ModuleInstance* instance);

  uhdm::Any* makeVar_(DesignComponent* component, Signal* sig,
                      std::vector<uhdm::Range*>* packedDimensions,
                      int32_t packedSize,
                      std::vector<uhdm::Range*>* unpackedDimensions,
                      int32_t unpackedSize, ModuleInstance* instance,
                      uhdm::VariablesCollection* vars, uhdm::Expr* assignExp,
                      uhdm::Typespec* tps);

  void swapTypespecPointersInUhdm(
      uhdm::Serializer& s,
      std::map<const uhdm::Typespec*, const uhdm::Typespec*>& typespecSwapMap);
  void swapTypespecPointersInTypedef(
      Design* design,
      std::map<const uhdm::Typespec*, const uhdm::Typespec*>& typespecSwapMap);

 protected:
  Session* const m_session = nullptr;
  CompileDesign* const m_compileDesign = nullptr;
  ExprBuilder m_exprBuilder;
  CompileHelper m_helper;
  std::map<std::string, Variable*> m_staticVariables;
};

};  // namespace SURELOG

#endif /* SURELOG_ELABORATIONSTEP_H */
