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
 * File:   Program.h
 * Author: alain
 *
 * Created on June 1, 2018, 8:58 PM
 */

#ifndef SURELOG_PROGRAM_H
#define SURELOG_PROGRAM_H
#pragma once

#include <Surelog/Common/ClockingBlockHolder.h>
#include <Surelog/Common/Containers.h>
#include <Surelog/Common/SymbolId.h>
#include <Surelog/Design/DesignComponent.h>

// UHDM
#include <uhdm/containers.h>

namespace SURELOG {

class CompileProgram;
class FileContent;
class Library;

class Program final : public DesignComponent, public ClockingBlockHolder {
  SURELOG_IMPLEMENT_RTTI(Program, DesignComponent)
  friend class CompileProgram;

 public:
  Program(std::string_view name, Library* library, FileContent* fC,
          NodeId nodeId);
  ~Program() final = default;

  uint32_t getSize() const final;
  VObjectType getType() const final;
  bool isInstance() const final { return true; }
  std::string_view getName() const final { return m_name; }

  ClassNameClassDefinitionMultiMap& getClassDefinitions() {
    return m_classDefinitions;
  }
  void addClassDefinition(std::string_view className,
                          ClassDefinition* classDef) {
    m_classDefinitions.emplace(className, classDef);
  }
  ClassDefinition* getClassDefinition(std::string_view name);

  UHDM::VectorOfattribute* Attributes() { return attributes_; }

  bool Attributes(UHDM::VectorOfattribute* data) {
    attributes_ = data;
    return true;
  }

  std::string_view getEndLabel() const { return m_endLabel; }
  void setEndLabel(std::string_view endLabel) { m_endLabel = endLabel; }

 private:
  std::string m_name;
  std::string m_endLabel;
  Library* m_library;
  ClassNameClassDefinitionMultiMap m_classDefinitions;

  UHDM::VectorOfattribute* attributes_ = nullptr;
};

};  // namespace SURELOG

#endif /* SURELOG_PROGRAM_H */
