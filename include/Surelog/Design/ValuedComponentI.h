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
 * File:   ValuedComponent.h
 * Author: alain
 *
 * Created on April 24, 2018, 8:46 PM
 */

#ifndef SURELOG_VALUEDCOMPONENTI_H
#define SURELOG_VALUEDCOMPONENTI_H
#pragma once

#include <Surelog/Common/RTTI.h>

// UHDM
#include <uhdm/uhdm_forward_decl.h>

#include <map>
#include <string>

namespace SURELOG {

class ExprBuilder;
class Value;

class ValuedComponentI : public RTTI {
  SURELOG_IMPLEMENT_RTTI(ValuedComponentI, RTTI)
 public:
  ValuedComponentI(const ValuedComponentI* parentScope,
                   ValuedComponentI* definition)
      : m_parentScope(parentScope), m_definition(definition){};

  ~ValuedComponentI() override = default;

  virtual Value* getValue(const std::string& name) const;
  virtual Value* getValue(const std::string& name,
                          ExprBuilder& exprBuilder) const;
  virtual void setValue(const std::string& name, Value* val,         // NOLINT
                        ExprBuilder& exprBuilder, int lineNb = 0);
  virtual void deleteValue(const std::string& name, ExprBuilder& exprBuilder);
  virtual void forgetValue(const std::string& name);
  std::map<std::string, std::pair<Value*, int>>& getMappedValues() {
    return m_paramMap;
  }
  const ValuedComponentI* getParentScope() const { return m_parentScope; }
  void setParentScope(ValuedComponentI* parent) { m_parentScope = parent; }

  virtual void setComplexValue(const std::string& name, UHDM::expr* val);
  virtual UHDM::expr* getComplexValue(const std::string& name) const;
  virtual void forgetComplexValue(const std::string& name);
  std::map<std::string, UHDM::expr*>& getComplexValues() {
    return m_complexValues;
  }
  // Do not change the signature of this method, it's use in gdb for debug.
  virtual std::string decompile(char* valueName) { return "Undefined"; }

 private:
  const ValuedComponentI* m_parentScope;
  ValuedComponentI* const m_definition;  // Module def for an instance
  std::map<std::string, std::pair<Value*, int>> m_paramMap;
  std::map<std::string, UHDM::expr*> m_complexValues;
};

}  // namespace SURELOG
SURELOG_IMPLEMENT_RTTI_VIRTUAL_CAST_FUNCTIONS(valuedcomponenti_cast,
                                              SURELOG::ValuedComponentI)

#endif /* SURELOG_VALUEDCOMPONENTI_H */
