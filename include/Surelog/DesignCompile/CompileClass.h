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
 * File:   CompileClass.h
 * Author: alain
 *
 * Created on June 7, 2018, 10:26 PM
 */

#ifndef SURELOG_COMPILECLASS_H
#define SURELOG_COMPILECLASS_H
#pragma once

#include <Surelog/DesignCompile/CompileHelper.h>
#include <Surelog/Testbench/ClassDefinition.h>

#include <cstdint>
#include <set>
#include <string>

// UHDM
#include <uhdm/containers.h>

namespace SURELOG {
class Session;

struct FunctorCompileClass final {
  FunctorCompileClass(Session* session, CompileDesign* compiler,
                      ClassDefinition* classDef, Design* design)
      : m_session(session),
        m_compileDesign(compiler),
        m_class(classDef),
        m_design(design) {}
  FunctorCompileClass(const FunctorCompileClass&) = delete;
  int32_t operator()() const;

 private:
  Session* const m_session = nullptr;
  CompileDesign* const m_compileDesign = nullptr;
  ClassDefinition* const m_class = nullptr;
  Design* const m_design = nullptr;
};

class CompileClass final {
 public:
  CompileClass(Session* session, CompileDesign* compiler,
               ClassDefinition* classDef, Design* design)
      : m_session(session),
        m_compileDesign(compiler),
        m_class(classDef),
        m_design(design),
        m_helper(session),
        m_builtins({"constraint_mode", "randomize", "rand_mode", "srandom"}) {}
  CompileClass(const CompileClass&) = delete;

  bool compile(Elaborate elaborate, Reduce reduce);

 private:
  bool compile_class_parameters_(const FileContent* fC, NodeId id);
  bool compile_class_property_(const FileContent* fC, NodeId id);
  bool compile_class_method_(const FileContent* fC, NodeId id);
  bool compile_class_constraint_(const FileContent* fC, NodeId id);
  bool compile_class_declaration_(const FileContent* fC, NodeId id);
  bool compile_covergroup_declaration_(const FileContent* fC, NodeId id);
  bool compile_local_parameter_declaration_(const FileContent* fC, NodeId id);
  bool compile_parameter_declaration_(const FileContent* fC, NodeId id);
  bool compile_class_type_(const FileContent* fC, NodeId id);
  bool compile_properties();

  Session* const m_session = nullptr;
  CompileDesign* const m_compileDesign = nullptr;
  ClassDefinition* const m_class = nullptr;
  Design* const m_design = nullptr;
  CompileHelper m_helper;
  uhdm::AttributeCollection* m_attributes = nullptr;
  const std::set<std::string> m_builtins;
};

}  // namespace SURELOG

#endif /* SURELOG_COMPILECLASS_H */
