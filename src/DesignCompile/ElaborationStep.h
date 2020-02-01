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

namespace SURELOG {

class ElaborationStep {
 public:
  ElaborationStep(CompileDesign* compileDesign)
      : m_compileDesign(compileDesign) {}
  ElaborationStep(const ElaborationStep& orig) = delete;

  virtual bool elaborate() = 0;

  virtual ~ElaborationStep();

 protected:
  DataType* bindTypeDef_(TypeDef* typd, DesignComponent* parent,
                         ErrorDefinition::ErrorType errtype);

  DataType* bindDataType_(std::string type_name, FileContent* fC, NodeId id,
                          DesignComponent* parent,
                          ErrorDefinition::ErrorType errtype);

  Variable* bindVariable_(std::string var_name, Scope* scope, FileContent* fc,
                          NodeId id, DesignComponent* parent,
                          ErrorDefinition::ErrorType errtype,
                          bool returnClassParam);

  Variable* locateVariable_(std::vector<std::string>& var_chain,
                            FileContent* fC, NodeId id, Scope* scope,
                            DesignComponent* parentComponent,
                            ErrorDefinition::ErrorType errtype);

  Variable* locateStaticVariable_(std::vector<std::string>& var_chain,
                                  FileContent* fC, NodeId id, Scope* scope,
                                  DesignComponent* parentComponent,
                                  ErrorDefinition::ErrorType errtype);

  bool bindPortType_(Signal* port,
                     FileContent* fC, NodeId id, Scope* scope,
                     DesignComponent* parentComponent,
                     ErrorDefinition::ErrorType errtype);
  
  CompileDesign* m_compileDesign;

  std::map<std::string, Variable*> m_staticVariables;
};

};  // namespace SURELOG

#endif /* ELABORATIONSTEP_H */
