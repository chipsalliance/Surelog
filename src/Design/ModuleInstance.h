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
 * File:   ModuleInstance.h
 * Author: alain
 *
 * Created on October 16, 2017, 10:48 PM
 */

#ifndef MODULEINSTANCE_H
#define MODULEINSTANCE_H

#include "Design/ModuleDefinition.h"
#include "Expression/Value.h"
#include "Expression/ExprBuilder.h"
#include "Design/ValuedComponentI.h"
#include "Design/Netlist.h"

namespace SURELOG {

class ModuleInstance : public ValuedComponentI {
 public:
  ModuleInstance(DesignComponent* definition, const FileContent* fileContent,
                 NodeId nodeId, ModuleInstance* parent, std::string instName,
                 std::string moduleName);
  ~ModuleInstance() override;
  void addSubInstances(ModuleInstance** subInstances,
                       unsigned int nbSubInstances);
  DesignComponent* getDefinition() { return m_definition; }
  unsigned int getNbChildren() { return m_nbChildren; }
  ModuleInstance* getChildren(unsigned int i) {
    if (m_children != NULL) {
      return m_children[i];
    } else {
      return NULL;
    }
  }
  ModuleInstance* getParent() { return m_parent; }
  const FileContent* getFileContent() { return m_fileContent; }
  SymbolId getFileId() const { return m_fileContent->getFileId(m_nodeId); }
  std::string getFileName() { return m_fileContent->getFileName(m_nodeId); }
  NodeId getNodeId() { return m_nodeId; }
  unsigned int getLineNb();
  VObjectType getType();
  VObjectType getModuleType();
  SymbolId getFullPathId(SymbolTable* symbols);
  SymbolId getInstanceId(SymbolTable* symbols);
  SymbolId getModuleNameId(SymbolTable* symbols);
  std::string getInstanceName();
  std::string getFullPathName();
  std::string getModuleName();
  unsigned int getDepth();

  void setNodeId(NodeId id) { m_nodeId = id; }  // Used for generate stmt
  void overrideParentChild(ModuleInstance* parent, ModuleInstance* interm,
                           ModuleInstance* child);
  Netlist* getNetlist() { return m_netlist; }
  void setNetlist(Netlist* netlist) { m_netlist = netlist; }

  std::vector<Parameter*>& getTypeParams() { return m_typeParams; }   

  Value* getValue(const std::string& name, ExprBuilder& exprBuilder) const override;

 private:
  DesignComponent* m_definition;
  ModuleInstance** m_children;
  unsigned int m_nbChildren;
  const FileContent* m_fileContent;
  NodeId m_nodeId;
  ModuleInstance* m_parent;
  std::string m_instName;  // Can carry the moduleName@instanceName if the
                           // module is undefined
  std::vector<Parameter*> m_typeParams;                         
  Netlist* m_netlist;
};

class ModuleInstanceFactory {
 public:
  ModuleInstance* newModuleInstance(DesignComponent* definition,
                                    const FileContent* fileContent,
                                    NodeId nodeId,
                                    ModuleInstance* parent,
                                    std::string instName,
                                    std::string moduleName);
};

}  // namespace SURELOG

#endif /* MODULEINSTANCE_H */
