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

#ifndef ELABORATIONSTEP_H
#define ELABORATIONSTEP_H

#include "DesignCompile/CompileDesign.h"
#include "headers/uhdm_forward_decl.h"

namespace SURELOG {

class ElaborationStep {
 public:
  ElaborationStep(CompileDesign* compileDesign);
  ElaborationStep(const ElaborationStep& orig) = delete;

  virtual bool elaborate() = 0;

  virtual ~ElaborationStep();

 protected:
  bool bindTypedefs_();
  
  const DataType* bindTypeDef_(TypeDef* typd,
                               const DesignComponent* parent,
                               ErrorDefinition::ErrorType errtype);

  const DataType* bindDataType_(const std::string& type_name,
                                const FileContent* fC, NodeId id,
                                const DesignComponent* parent,
                                ErrorDefinition::ErrorType errtype);

  Variable* bindVariable_(std::string var_name, Scope* scope,
                          const FileContent* fc,
                          NodeId id, const DesignComponent* parent,
                          ErrorDefinition::ErrorType errtype,
                          bool returnClassParam);

  Variable* locateVariable_(std::vector<std::string>& var_chain,
                            const FileContent* fC, NodeId id, Scope* scope,
                            DesignComponent* parentComponent,
                            ErrorDefinition::ErrorType errtype);

  Variable* locateStaticVariable_(std::vector<std::string>& var_chain,
                                  const FileContent* fC, NodeId id,
                                  Scope* scope,
                                  DesignComponent* parentComponent,
                                  ErrorDefinition::ErrorType errtype);

  bool bindPortType_(Signal* port,
                     const FileContent* fC, NodeId id, Scope* scope,
                     DesignComponent* parentComponent,
                     ErrorDefinition::ErrorType errtype);

  UHDM::expr* exprFromAssign_(DesignComponent* component, const FileContent* fC, NodeId id, NodeId unpackedDimension, ModuleInstance* instance);

  UHDM::typespec* elabTypeParameter_(DesignComponent* component, Parameter* typeParam, ModuleInstance* instance);

  UHDM::any* makeVar_(DesignComponent* component, Signal* sig, std::vector<UHDM::range*>* packedDimensions, int packedSize, 
                std::vector<UHDM::range*>* unpackedDimensions, int unpackedSize, ModuleInstance* instance, 
                UHDM::VectorOfvariables* vars, UHDM::expr* assignExp, UHDM::typespec* tps);

  CompileDesign* m_compileDesign;
  ExprBuilder m_exprBuilder;
  SymbolTable* m_symbols;
  ErrorContainer* m_errors;
  CompileHelper m_helper;

  std::map<std::string, Variable*> m_staticVariables;
};

};  // namespace SURELOG

#endif /* ELABORATIONSTEP_H */
