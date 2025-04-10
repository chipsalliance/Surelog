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
 * File:   Precompiled.h
 * Author: alain
 *
 * Created on April 28, 2018, 10:27 AM
 */

#ifndef SURELOG_PRECOMPILED_H
#define SURELOG_PRECOMPILED_H
#pragma once

#include <functional>
#include <map>
#include <set>
#include <string>
#include <string_view>

namespace SURELOG {
class PathId;
class SymbolTable;

class Precompiled final {
 public:
  static Precompiled* getSingleton();
  Precompiled(const Precompiled&) = delete;

  void addPrecompiled(std::string_view package_name, std::string_view fileName);

  std::string getFileName(std::string_view packageName) const;

  bool isFilePrecompiled(PathId fileId, SymbolTable* symbolTable) const;
  bool isFilePrecompiled(std::string_view fileName) const;

  bool isPackagePrecompiled(std::string_view packageName) const;

 private:
  Precompiled();  // Only accessed via singleton.

  std::map<std::string, std::string, std::less<>> m_packageMap;
  std::set<std::string, std::less<>> m_packageFileSet;
};

}  // namespace SURELOG

#endif /* PRECOMPILED_H */
