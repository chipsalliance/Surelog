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

#ifndef RESOLVESYMBOLS_H
#define RESOLVESYMBOLS_H
#include "Design/TimeInfo.h"
#include "Design/FileContent.h"
#include "DesignCompile/CompileStep.h"

namespace SURELOG {

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
  CompileDesign* m_compileDesign;
  FileContent* m_fileData;
  SymbolTable* m_symbolTable;
  ErrorContainer* m_errorContainer;
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
  CompileDesign* m_compileDesign;
  FileContent* m_fileData;
  SymbolTable* m_symbolTable;
  ErrorContainer* m_errorContainer;
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

  const VObject Object(NodeId index) const override;
  VObject* MutableObject(NodeId index);

  NodeId UniqueId(NodeId index) override;

  SymbolId Name(NodeId index) override;

  NodeId Child(NodeId index) override;

  NodeId Sibling(NodeId index) override;

  NodeId Definition(NodeId index) const override;
  bool SetDefinition(NodeId index, NodeId node);

  NodeId Parent(NodeId index) override;

  unsigned short Type(NodeId index) const override;
  bool SetType(NodeId index, unsigned short type);

  unsigned int Line(NodeId index) override;

  std::string Symbol(SymbolId id) override;

  std::string SymName(NodeId index) override;

  NodeId sl_get(NodeId parent, VObjectType type) override;  // Get first item of type

  NodeId sl_parent(NodeId parent,
                   VObjectType type) override;  // Get first parent item of type

  NodeId sl_parent(NodeId parent, std::vector<VObjectType> types,
                   VObjectType& actualType) override;

  std::vector<NodeId> sl_get_all(NodeId parent,
                                 VObjectType type) override;  // get all items of type

  NodeId sl_collect(
      NodeId parent,
      VObjectType type) override;  // Recursively search for first item of type

  std::vector<NodeId> sl_collect_all(
      NodeId parent,
      VObjectType type) override;  // Recursively search for all items of type

  ResolveSymbols(const ResolveSymbols& orig);
  ~ResolveSymbols() override;

  Compiler* getCompiler() { return m_compileDesign->getCompiler(); }

 private:
  bool bindDefinition_(unsigned int objIndex,
                       std::vector<VObjectType> bindTypes);

  CompileDesign* m_compileDesign;
  FileContent* m_fileData;
  SymbolTable* m_symbolTable;
  ErrorContainer* m_errorContainer;
};

};  // namespace SURELOG

#endif /* RESOLVESYMBOLS_H */
