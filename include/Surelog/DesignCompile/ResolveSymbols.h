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
 * File:   ResolveSymbols.h
 * Author: alain
 *
 * Created on July 1, 2017, 12:38 PM
 */

#ifndef SURELOG_RESOLVESYMBOLS_H
#define SURELOG_RESOLVESYMBOLS_H
#pragma once

#include <Surelog/Common/NodeId.h>
#include <Surelog/Common/SymbolId.h>
#include <Surelog/DesignCompile/CompileStep.h>
#include <Surelog/SourceCompile/VObjectTypes.h>

#include <cstdint>
#include <string_view>
#include <unordered_set>
#include <vector>

namespace SURELOG {
class CompileDesign;
class Compiler;
class Design;
class FileContent;
class Session;

struct FunctorCreateLookup final {
  FunctorCreateLookup(Session* session, CompileDesign* compileDesign,
                      FileContent* fileContent, Design* design)
      : m_session(session),
        m_compileDesign(compileDesign),
        m_fileContent(fileContent) {}
  FunctorCreateLookup(const FunctorCreateLookup&) = delete;
  int32_t operator()() const;

 private:
  Session* const m_session = nullptr;
  CompileDesign* const m_compileDesign = nullptr;
  FileContent* const m_fileContent = nullptr;
};

struct FunctorResolve final {
  FunctorResolve(Session* session, CompileDesign* compileDesign,
                 FileContent* fileContent, Design* design)
      : m_session(session),
        m_compileDesign(compileDesign),
        m_fileContent(fileContent) {}
  FunctorResolve(const FunctorResolve&) = delete;
  int32_t operator()() const;

 private:
  Session* const m_session = nullptr;
  CompileDesign* const m_compileDesign = nullptr;
  FileContent* const m_fileContent = nullptr;
};

class ResolveSymbols final : public CompileStep {
 public:
  ResolveSymbols(Session* session, CompileDesign* compileDesign,
                 FileContent* fileContent)
      : m_session(session),
        m_compileDesign(compileDesign),
        m_fileContent(fileContent) {}
  ResolveSymbols(const ResolveSymbols&) = delete;
  ~ResolveSymbols() final = default;

  void createFastLookup();

  bool resolve();

  VObject Object(NodeId index) const final;
  VObject* MutableObject(NodeId index);

  NodeId UniqueId(NodeId index) const final;

  SymbolId Name(NodeId index) const final;

  NodeId Child(NodeId index) const final;

  NodeId Sibling(NodeId index) const final;

  NodeId Definition(NodeId index) const final;
  bool SetDefinition(NodeId index, NodeId node);

  NodeId Parent(NodeId index) const final;

  VObjectType Type(NodeId index) const final;
  bool SetType(NodeId index, VObjectType type);

  uint32_t Line(NodeId index) const final;

  std::string_view Symbol(SymbolId id) const final;

  std::string_view SymName(NodeId index) const final;

  NodeId sl_get(NodeId parent,
                VObjectType type) const final;  // Get first item of type

  NodeId sl_parent(
      NodeId parent,
      VObjectType type) const final;  // Get first parent item of type

  NodeId sl_parent(NodeId parent, const VObjectTypeUnorderedSet& types,
                   VObjectType& actualType) const final;

  std::vector<NodeId> sl_get_all(
      NodeId parent,
      VObjectType type) const final;  // get all items of type

  NodeId sl_collect(NodeId parent,
                    VObjectType type)
      const final;  // Recursively search for first item of type

  std::vector<NodeId> sl_collect_all(NodeId parent,
                                     VObjectType type)
      const final;  // Recursively search for all items of type

  Compiler* getCompiler() const;

 private:
  bool bindDefinition_(NodeId objIndex,
                       const VObjectTypeUnorderedSet& bindTypes);

  Session* const m_session = nullptr;
  CompileDesign* const m_compileDesign = nullptr;
  FileContent* const m_fileContent = nullptr;
};

};  // namespace SURELOG

#endif /* SURELOG_RESOLVESYMBOLS_H */
