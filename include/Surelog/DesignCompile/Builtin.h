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
 * File:   Builtin.h
 * Author: alain
 *
 * Created on May 30, 2019, 6:36 PM
 */

#ifndef SURELOG_BUILTIN_H
#define SURELOG_BUILTIN_H
#pragma once

namespace SURELOG {

class CompilationUnit;
class CompileDesign;
class Design;
class Session;
class SymbolTable;

// TODO: this looks like it should probably be more a
// function ? Something like
// SURELOG::addBuiltinsTo(Design *design);
class Builtin final {
 public:
  Builtin(Session* session, CompileDesign* compileDesign, Design* design);
  void addBuiltinMacros(CompilationUnit* compUnit) const;
  void addBuiltinTypes() const;
  void addBuiltinClasses() const;

 private:
  Session* const m_session = nullptr;
  CompileDesign* const m_compileDesign = nullptr;
  Design* const m_design = nullptr;
};

};  // namespace SURELOG

#endif /* SURELOG_BUILTIN_H */
