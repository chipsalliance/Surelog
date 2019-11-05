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

#ifndef PROGRAM_H
#define PROGRAM_H
#include "../Design/DesignComponent.h"
#include "../Common/ClockingBlockHolder.h"

namespace SURELOG {

class CompileProgram;

class Program : public DesignComponent, public ClockingBlockHolder {
  friend class CompileProgram;

 public:
  Program(std::string name, Library* library, FileContent* fC, NodeId nodeId)
      : DesignComponent(fC), m_name(name), m_library(library) {
    addFileContent(fC, nodeId);
  }

  virtual ~Program();

  unsigned int getSize();
  VObjectType getType() { return (m_fileContents[0]->Type(m_nodeIds[0])); }
  bool isInstance() { return true; }
  std::string getName() { return m_name; }

  ClassNameClassDefinitionMultiMap& getClassDefinitions() {
    return m_classDefinitions;
  }
  void addClassDefinition(std::string className, ClassDefinition* classDef) {
    m_classDefinitions.insert(std::make_pair(className, classDef));
  }
  ClassDefinition* getClassDefinition(const std::string& name);

 private:
  std::string m_name;
  Library* m_library;
  ClassNameClassDefinitionMultiMap m_classDefinitions;
};

};  // namespace SURELOG

#endif /* PROGRAM_H */
