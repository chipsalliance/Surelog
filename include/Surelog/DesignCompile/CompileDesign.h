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

#include <map>
#include <vector>
#include <Surelog/Design/Design.h>

// UHDM
#include <uhdm/Serializer.h>
#include <uhdm/sv_vpi_user.h>

#include <mutex>

namespace SURELOG {

class Compiler;
class SymbolTable;
class ValuedComponentI;

void decompile(ValuedComponentI* instance);

class CompileDesign {
 public:
  // Note: takes owernship of compiler
  explicit CompileDesign(Compiler* compiler);
  virtual ~CompileDesign();  // Used in MockCompileDesign

  bool compile();
  bool elaborate();
  void purgeParsers();
  vpiHandle writeUHDM(PathId fileId);

  Compiler* getCompiler() const { return m_compiler; }
  virtual UHDM::Serializer& getSerializer() { return m_serializer; }
  void lockSerializer() { m_serializerMutex.lock(); }
  void unlockSerializer() { m_serializerMutex.unlock(); }
  UHDM::VectorOfinclude_file_info* getFileInfo() { return m_fileInfo; }
  std::map<const UHDM::typespec*, const UHDM::typespec*>& getSwapedObjects() { return m_typespecSwapMap; }
 private:
  CompileDesign(const CompileDesign& orig) = delete;

  template <class ObjectType, class ObjectMapType, typename FunctorType>
  void compileMT_(ObjectMapType& objects, int32_t maxThreadCount);

  void collectObjects_(Design::FileIdDesignContentMap& all_files,
                       Design* design, bool finalCollection);
  bool compilation_();
  bool elaboration_();

  Compiler* const m_compiler;
  std::vector<SymbolTable*> m_symbolTables;
  std::vector<ErrorContainer*> m_errorContainers;
  UHDM::VectorOfinclude_file_info* m_fileInfo = nullptr;
  std::mutex m_serializerMutex;
  UHDM::Serializer m_serializer;
  std::map<const UHDM::typespec*, const UHDM::typespec*> m_typespecSwapMap;
};

}  // namespace SURELOG

#endif /* SURELOG_COMPILEDESIGN_H */
