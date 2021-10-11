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
 * File:   Precompiled.cpp
 * Author: alain
 *
 * Created on April 28, 2018, 10:27 AM
 */

#include "Package/Precompiled.h"

Precompiled::Precompiled() {
  addPrecompiled("uvm_pkg", "uvm_pkg.sv");
  addPrecompiled("ovm_pkg", "ovm_pkg.sv");
}

Precompiled* Precompiled::getSingleton() {
  static Precompiled* const singleton = new Precompiled();
  return singleton;
}

void Precompiled::addPrecompiled(std::string_view packageName,
                                 std::string_view fileName) {
  m_packageMap.insert({std::string(packageName), std::string(fileName)});
  m_packageFileSet.insert(std::string(fileName));
}

std::string Precompiled::getFileName(std::string_view packageName) const {
  auto found = m_packageMap.find(packageName);
  return (found == m_packageMap.end()) ? "" : found->second;
}

bool Precompiled::isFilePrecompiled(std::string_view fileName) const {
  auto found = m_packageFileSet.find(fileName);
  return (found != m_packageFileSet.end());
}

bool Precompiled::isPackagePrecompiled(std::string_view packageName) const {
  auto found = m_packageMap.find(packageName);
  return (found != m_packageMap.end());
}
