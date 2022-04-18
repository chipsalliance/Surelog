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

#include <Surelog/Common/SymbolId.h>
#include <Surelog/DesignCompile/CompileStep.h>

namespace SURELOG {

class Compiler;
class CompileDesign;
class Design;
class ErrorContainer;
class FileContent;
class SymbolTable;

struct FunctorCreateLookup {
  FunctorCreateLookup(CompileDesign* compileDesign, FileContent* fileContent,
                      Design* design, SymbolTable* symbolTable,
                      ErrorContainer* errors)
      : m_compileDesign(compileDesign),
        m_fileData(fileContent),
        m_symbolTable(symbolTable),
        m_errorContainer(errors) {}
  int operator()() const;

 private:
  CompileDesign* const m_compileDesign;
  FileContent* const m_fileData;
  SymbolTable* const m_symbolTable;
  ErrorContainer* const m_errorContainer;
};

struct FunctorResolve {
  FunctorResolve(CompileDesign* compileDesign, FileContent* fileContent,
                 Design* design, SymbolTable* symbolTable,
                 ErrorContainer* errors)
      : m_compileDesign(compileDesign),
        m_fileData(fileContent),
        m_symbolTable(symbolTable),
        m_errorContainer(errors) {}
  int operator()() const;

 private:
  CompileDesign* const m_compileDesign;
  FileContent* const m_fileData;
  SymbolTable* const m_symbolTable;
  ErrorContainer* const m_errorContainer;
};

class ResolveSymbols : public CompileStep {
 public:
  ResolveSymbols(CompileDesign* compileDesign, FileContent* fileContent,
                 SymbolTable* symbolTable, ErrorContainer* errors)
      : m_compileDesign(compileDesign),
        m_fileData(fileContent),
        m_symbolTable(symbolTable),
        m_errorContainer(errors) {}

  void createFastLookup();

  bool resolve();

  VObject Object(NodeId index) const override;
  VObject* MutableObject(NodeId index);

  NodeId UniqueId(NodeId index) override;

  SymbolId Name(NodeId index) override;

  NodeId Child(NodeId index) override;

  NodeId Sibling(NodeId index) override;

  NodeId Definition(NodeId index) const override;
  bool SetDefinition(NodeId index, NodeId node);

  NodeId Parent(NodeId index) override;

  VObjectType Type(NodeId index) const override;
  bool SetType(NodeId index, VObjectType type);

  unsigned int Line(NodeId index) override;

  std::string Symbol(SymbolId id) override;

  std::string SymName(NodeId index) override;

  NodeId sl_get(NodeId parent,
                VObjectType type) override;  // Get first item of type

  NodeId sl_parent(NodeId parent,
                   VObjectType type) override;  // Get first parent item of type

  NodeId sl_parent(NodeId parent, std::vector<VObjectType> types,
                   VObjectType& actualType) override;

  std::vector<NodeId> sl_get_all(
      NodeId parent,
      VObjectType type) override;  // get all items of type

  NodeId sl_collect(
      NodeId parent,
      VObjectType type) override;  // Recursively search for first item of type

  std::vector<NodeId> sl_collect_all(
      NodeId parent,
      VObjectType type) override;  // Recursively search for all items of type

  ResolveSymbols(const ResolveSymbols& orig);
  ~ResolveSymbols() override = default;

  Compiler* getCompiler() const;

 private:
  bool bindDefinition_(unsigned int objIndex,
                       const std::vector<VObjectType>& bindTypes);

  CompileDesign* const m_compileDesign;
  FileContent* const m_fileData;
  SymbolTable* const m_symbolTable;
  ErrorContainer* const m_errorContainer;
};

};  // namespace SURELOG

#endif /* SURELOG_RESOLVESYMBOLS_H */
