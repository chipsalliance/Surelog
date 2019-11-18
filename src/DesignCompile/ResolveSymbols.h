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
#include "CompileStep.h"

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

  VObject& Object(NodeId index);

  NodeId UniqueId(NodeId index);

  SymbolId Name(NodeId index);

  NodeId Child(NodeId index);

  NodeId Sibling(NodeId index);

  NodeId& Definition(NodeId index);

  NodeId Parent(NodeId index);

  unsigned short& Type(NodeId index);

  unsigned int Line(NodeId index);

  std::string Symbol(SymbolId id);

  std::string SymName(NodeId index);

  NodeId sl_get(NodeId parent, VObjectType type);  // Get first item of type

  NodeId sl_parent(NodeId parent,
                   VObjectType type);  // Get first parent item of type

  NodeId sl_parent(NodeId parent, std::vector<VObjectType> types,
                   VObjectType& actualType);

  std::vector<NodeId> sl_get_all(NodeId parent,
                                 VObjectType type);  // get all items of type

  NodeId sl_collect(
      NodeId parent,
      VObjectType type);  // Recursively search for first item of type

  std::vector<NodeId> sl_collect_all(
      NodeId parent,
      VObjectType type);  // Recursively search for all items of type

  ResolveSymbols(const ResolveSymbols& orig);
  virtual ~ResolveSymbols();

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
