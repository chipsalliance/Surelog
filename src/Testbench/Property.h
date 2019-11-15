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
 * File:   Property.h
 * Author: alain
 *
 * Created on January 23, 2019, 9:17 PM
 */

#ifndef PROPERTY_H
#define PROPERTY_H

#include "../Design/DataType.h"
#include "Variable.h"

namespace SURELOG {

class Property : public Variable {
 public:
  Property(DataType* dataType, FileContent* fc, NodeId varId, NodeId range,
           std::string name, bool is_local, bool is_static, bool is_protected,
           bool is_rand, bool is_randc)
      : Variable(dataType, fc, varId, range, name),
        m_is_local(is_local),
        m_is_static(is_static),
        m_is_protected(is_protected),
        m_is_rand(is_rand),
        m_is_randc(is_randc) {}
  virtual ~Property();

  bool isLocal() { return m_is_local; }
  bool isStatic() { return m_is_static; }
  bool isProtected() { return m_is_protected; }
  bool isRand() { return m_is_rand; }
  bool isRandc() { return m_is_randc; }

 private:
  bool m_is_local;
  bool m_is_static;
  bool m_is_protected;
  bool m_is_rand;
  bool m_is_randc;
};

};  // namespace SURELOG

#endif /* PROPERTY_H */
