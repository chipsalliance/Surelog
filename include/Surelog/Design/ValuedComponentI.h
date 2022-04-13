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
#include <Surelog/Common/Containers.h>

// UHDM
#include <uhdm/uhdm_forward_decl.h>

#include <map>
#include <string>
#include <string_view>

namespace SURELOG {

class ExprBuilder;
class Value;

class ValuedComponentI : public RTTI {
  SURELOG_IMPLEMENT_RTTI(ValuedComponentI, RTTI)
 public:
  using ParamMap = std::map<std::string, std::pair<Value*, int>, StringViewCompare>;
  using ComplexValueMap = std::map<std::string, UHDM::expr*, StringViewCompare>;

  ValuedComponentI(const ValuedComponentI* parentScope,
                   ValuedComponentI* definition)
      : m_parentScope(parentScope), m_definition(definition){};

  ~ValuedComponentI() override = default;

  virtual Value* getValue(std::string_view name) const;
  virtual Value* getValue(std::string_view name,
                          ExprBuilder& exprBuilder) const;
  virtual void setValue(std::string_view name, Value* val,         // NOLINT
                        ExprBuilder& exprBuilder, int lineNb = 0);
  virtual void deleteValue(std::string_view name, ExprBuilder& exprBuilder);
  virtual void forgetValue(std::string_view name);
  const ParamMap& getMappedValues() const {
    return m_paramMap;
  }
  const ValuedComponentI* getParentScope() const { return m_parentScope; }
  void setParentScope(ValuedComponentI* parent) { m_parentScope = parent; }

  virtual void setComplexValue(std::string_view name, UHDM::expr* val);
  virtual UHDM::expr* getComplexValue(std::string_view name) const;
  virtual void forgetComplexValue(std::string_view name);
  const ComplexValueMap& getComplexValues() const {
    return m_complexValues;
  }
  // Do not change the signature of this method, it's use in gdb for debug.
  virtual std::string decompile(char* valueName) { return "Undefined"; }

 private:
  const ValuedComponentI* m_parentScope;
  ValuedComponentI* const m_definition;  // Module def for an instance
  ParamMap m_paramMap;
  ComplexValueMap m_complexValues;
};

}  // namespace SURELOG
SURELOG_IMPLEMENT_RTTI_VIRTUAL_CAST_FUNCTIONS(valuedcomponenti_cast,
                                              SURELOG::ValuedComponentI)

#endif /* SURELOG_VALUEDCOMPONENTI_H */
