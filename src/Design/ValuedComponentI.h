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

#ifndef VALUEDCOMPONENTI_H
#define VALUEDCOMPONENTI_H

namespace SURELOG {

class ExprBuilder;

class ValuedComponentI {
 public:
  ValuedComponentI(ValuedComponentI* parentScope, ValuedComponentI* definition)
      : m_parentScope(parentScope), m_definition(definition) {};
  virtual ~ValuedComponentI(){};
  virtual Value* getValue(std::string name);
  virtual void setValue(std::string name, Value* val, ExprBuilder& exprBuilder, int lineNb = 0);
  std::vector<Value*>& getValues() { return m_paramValues; }
  std::map<std::string, std::pair<Value*, int>>& getMappedValues() { return m_paramMap; }
  ValuedComponentI* getParentScope() { return m_parentScope; }

 private:
  ValuedComponentI* m_parentScope;
  ValuedComponentI* m_definition; // Module def for an instance
  std::vector<Value*> m_paramValues;
  std::map<std::string, std::pair<Value*, int>> m_paramMap;
};

};  // namespace SURELOG

#endif /* VALUEDCOMPONENTI_H */
