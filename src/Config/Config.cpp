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
 * File:   Config.cpp
 * Author: alain
 *
 * Created on February 10, 2018, 11:09 PM
 */

#include <Surelog/Config/Config.h>

namespace SURELOG {
UseClause* Config::getInstanceUseClause(std::string_view instance) {
  const auto found = m_instanceUseClauses.find(instance);
  return (found == m_instanceUseClauses.end()) ? nullptr : &found->second;
}

UseClause* Config::getCellUseClause(std::string_view cell) {
  const auto found = m_cellUseClauses.find(cell);
  return (found == m_cellUseClauses.end()) ? nullptr : &found->second;
}

void Config::addInstanceUseClause(std::string_view instance,
                                  const UseClause& use) {
  auto previous = m_instanceUseClauses.find(instance);
  if (previous != m_instanceUseClauses.end()) {
    m_instanceUseClauses.erase(previous);
  }

  m_instanceUseClauses.insert(std::make_pair(instance, use));
}
void Config::addCellUseClause(std::string_view cell, const UseClause& use) {
  auto previous = m_cellUseClauses.find(cell);
  if (previous != m_cellUseClauses.end()) {
    m_instanceUseClauses.erase(previous);
  }
  m_cellUseClauses.insert(std::make_pair(cell, use));
}
}  // namespace SURELOG
