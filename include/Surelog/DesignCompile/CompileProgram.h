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
 * File:   CompileProgram.h
 * Author: alain
 *
 * Created on June 6, 2018, 10:43 PM
 */

#ifndef SURELOG_COMPILEPROGRAM_H
#define SURELOG_COMPILEPROGRAM_H
#pragma once

#include <Surelog/DesignCompile/CompileHelper.h>
#include <Surelog/DesignCompile/CompileToolbox.h>
#include <uhdm/containers.h>

#include <cstdint>

namespace SURELOG {
class CompileDesign;
class Design;
class Program;
class Session;

struct FunctorCompileProgram final {
  FunctorCompileProgram(Session* session, CompileDesign* compileDesign,
                        Program* program, Design* design)
      : m_session(session),
        m_compileDesign(compileDesign),
        m_program(program),
        m_design(design) {}
  int32_t operator()() const;

 private:
  Session* const m_session = nullptr;
  CompileDesign* const m_compileDesign = nullptr;
  Program* const m_program = nullptr;
  Design* const m_design = nullptr;
};

class CompileProgram final : public CompileToolbox {
 public:
  CompileProgram(Session* session, CompileDesign* compileDesign,
                 Program* program, Design* design)
      : m_session(session),
        m_compileDesign(compileDesign),
        m_program(program),
        m_design(design),
        m_helper(session) {}

  bool compile(Elaborate elaborate, Reduce reduce);

  ~CompileProgram() final = default;

 private:
  enum CollectType { FUNCTION, DEFINITION, OTHER };
  bool collectObjects_(CollectType collectType);

  Session* const m_session = nullptr;
  CompileDesign* const m_compileDesign = nullptr;
  Program* const m_program = nullptr;
  Design* const m_design = nullptr;
  CompileHelper m_helper;
  uint32_t m_nbPorts = 0;
  bool m_hasNonNullPort = false;
  uhdm::AttributeCollection* m_attributes = nullptr;
};

}  // namespace SURELOG

#endif /* SURELOG_COMPILEPROGRAM_H */
