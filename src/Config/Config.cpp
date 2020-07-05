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
#include "SourceCompile/SymbolTable.h"
#include "Design/FileContent.h"
#include "Config/Config.h"
using namespace SURELOG;

UseClause* Config::getInstanceUseClause(const std::string& instance) {
  std::map<std::string, UseClause>::iterator itr =
      m_instanceUseClauses.find(instance);
  if (itr == m_instanceUseClauses.end()) {
    return NULL;
  } else {
    return &(*itr).second;
  }
}

UseClause* Config::getCellUseClause(const std::string& cell) {
  std::map<std::string, UseClause>::iterator itr = m_cellUseClauses.find(cell);
  if (itr == m_cellUseClauses.end()) {
    return NULL;
  } else {
    return &(*itr).second;
  }
}

void Config::addInstanceUseClause(const std::string& instance, UseClause use) {
  auto itr = m_instanceUseClauses.find(instance);
  if (itr != m_instanceUseClauses.end()) {
    m_instanceUseClauses.erase(itr);
  }

  m_instanceUseClauses.insert(std::make_pair(instance, use));
}
void Config::addCellUseClause(const std::string& cell, UseClause use) {
  auto itr = m_cellUseClauses.find(cell);
  if (itr != m_cellUseClauses.end()) {
    m_instanceUseClauses.erase(itr);
  }
  m_cellUseClauses.insert(std::make_pair(cell, use));
}
