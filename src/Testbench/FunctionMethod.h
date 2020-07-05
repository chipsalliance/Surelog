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
 * File:   FunctionMethod.h
 * Author: alain
 *
 * Created on February 21, 2019, 8:20 PM
 */

#ifndef FUNCTIONMETHOD_H
#define FUNCTIONMETHOD_H

#include "Design/Function.h"

namespace SURELOG {

class FunctionMethod : public Function {
 public:
  FunctionMethod(DesignComponent* parent, const FileContent* fC, NodeId id,
                 std::string name, DataType* returnType, bool is_virtual,
                 bool is_extern, bool is_static, bool is_local,
                 bool is_protected, bool is_pure)
      : Function(parent, fC, id, name, returnType),
        m_virtual(is_virtual),
        m_extern(is_extern),
        m_static(is_static),
        m_local(is_local),
        m_protected(is_protected),
        m_pure(is_pure) {}
  ~FunctionMethod() override;

  bool isVirtual() const { return m_virtual; }
  bool isExtern() const { return m_extern; }
  bool isStatic() const { return m_static; }
  bool isLocal() const { return m_local; }
  bool isProtected() const { return m_protected; }
  bool isPure() const { return m_pure; }
  bool compile(CompileHelper& compile_helper);

 private:
  bool m_virtual;
  bool m_extern;
  bool m_static;
  bool m_local;
  bool m_protected;
  bool m_pure;
};

};  // namespace SURELOG

#endif /* FUNCTIONMETHOD_H */
