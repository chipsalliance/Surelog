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
 * File:   CompileDesign.h
 * Author: alain
 *
 * Created on July 1, 2017, 1:11 PM
 */

#ifndef SURELOG_COMPILEDESIGN_H
#define SURELOG_COMPILEDESIGN_H
#pragma once

#include <Surelog/Common/PathId.h>
#include <Surelog/Design/Design.h>

#include <cstdint>
#include <map>
#include <vector>

// UHDM
#include <uhdm/Serializer.h>
#include <uhdm/containers.h>
#include <uhdm/sv_vpi_user.h>
#include <uhdm/typespec.h>
#include <uhdm/uhdm_forward_decl.h>

#include <mutex>

namespace uhdm {
class Serializer;
}

namespace SURELOG {
class Compiler;
class Session;
class SymbolTable;
class ValuedComponentI;

void decompile(Session* session, ValuedComponentI* instance);

class CompileDesign {
 public:
  // Note: takes owernship of compiler
  CompileDesign(Session* session, Compiler* compiler);
  CompileDesign(const CompileDesign& orig) = delete;
  virtual ~CompileDesign() = default;  // Used in MockCompileDesign

  bool compile();
  bool elaborate();
  void purgeParsers();
  bool writeUHDM(PathId fileId);

  Session* getSession() { return m_session; }
  const Session* getSession() const { return m_session; }

  Compiler* getCompiler() const { return m_compiler; }
  uhdm::Serializer& getSerializer();
  void lockSerializer();
  void unlockSerializer();
  uhdm::SourceFileCollection* getUhdmSourceFiles() { return m_uhdmSourcefiles; }
  std::map<const uhdm::Typespec*, const uhdm::Typespec*>& getSwapedObjects() {
    return m_typespecSwapMap;
  }

 private:
  template <class ObjectType, class ObjectMapType, typename FunctorType>
  void compileMT_(ObjectMapType& objects, int32_t maxThreadCount);

  void collectObjects_(Design::FileIdDesignContentMap& all_files,
                       Design* design, bool finalCollection);
  bool compilation_();
  bool elaboration_();

  Session* const m_session = nullptr;
  Compiler* const m_compiler = nullptr;
  std::vector<Session*> m_sessions;
  uhdm::SourceFileCollection* m_uhdmSourcefiles = nullptr;
  std::map<const uhdm::Typespec*, const uhdm::Typespec*> m_typespecSwapMap;
};

}  // namespace SURELOG

#endif /* SURELOG_COMPILEDESIGN_H */
