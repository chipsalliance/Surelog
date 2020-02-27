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
 * File:   Config.h
 * Author: alain
 *
 * Created on February 10, 2018, 11:09 PM
 */

#ifndef CONFIG_H
#define CONFIG_H

#include <string>
#include <vector>
#include <map>

namespace SURELOG {

class UseClause {
 public:
  enum Type { UseLib, UseConfig, UseModule, UseParam };
  UseClause(Type type, std::string name, FileContent* fC, NodeId id)
      : m_type(type),
        m_name(name),
        m_fileContent(fC),
        m_node(id),
        m_used(false) {}
  UseClause(Type type, FileContent* fC, NodeId id)
      : m_type(type),
        m_name(""),
        m_fileContent(fC),
        m_node(id),
        m_used(false) {}
  UseClause(Type type, std::vector<std::string>& libs, FileContent* fC,
            NodeId id)
      : m_type(type),
        m_name(""),
        m_libs(libs),
        m_fileContent(fC),
        m_node(id),
        m_used(false) {}
  Type getType() { return m_type; }
  std::string getName() { return m_name; }
  std::vector<std::string> getLibs() { return m_libs; }
  FileContent* getFileContent() { return m_fileContent; }
  NodeId getNodeId() { return m_node; }
  void setUsed() { m_used = true; }
  bool isUsed() { return m_used; }

 private:
  Type m_type;
  std::string m_name;
  std::vector<std::string> m_libs;
  FileContent* m_fileContent;
  NodeId m_node;
  bool m_used;
};

class Config {
 public:
  Config(std::string name, FileContent* fC, NodeId nodeId)
      : m_name(name),
        m_fileContent(fC),
        m_nodeId(nodeId),
        m_used(false),
        m_isTopLevel(false) {}
  void setIsUsed() { m_used = true; }
  void setDesignTop(std::string top) { m_designTop = top; }
  void setDesignLib(std::string lib) { m_designLib = lib; }
  void addDefaultLib(std::string lib) { m_defaultLibs.push_back(lib); }
  void addInstanceUseClause(std::string instance, UseClause use);
  void addCellUseClause(std::string cell, UseClause use);
  virtual ~Config();
  std::string getName() { return m_name; }
  FileContent* getFileContent() { return m_fileContent; }
  NodeId getNodeId() { return m_nodeId; }
  bool isUsed() { return m_used; }
  std::string getDesignTop() { return m_designTop; }
  std::string getDesignLib() { return m_designLib; }
  std::vector<std::string>& getDefaultLibs() { return m_defaultLibs; }
  std::map<std::string, UseClause>& getInstanceUseClauses() {
    return m_instanceUseClauses;
  }
  UseClause* getInstanceUseClause(std::string instance);
  std::map<std::string, UseClause>& getCellUseClauses() {
    return m_cellUseClauses;
  }
  UseClause* getCellUseClause(std::string cell);
  bool isTopLevel() { return m_isTopLevel; }
  void setTopLevel(bool top) { m_isTopLevel = top; }

 private:
  std::string m_name;
  FileContent* m_fileContent;
  NodeId m_nodeId;
  bool m_used;
  bool m_isTopLevel;
  std::string m_designLib;
  std::string m_designTop;
  std::vector<std::string> m_defaultLibs;
  std::map<std::string, UseClause> m_instanceUseClauses;
  std::map<std::string, UseClause> m_cellUseClauses;
};

};  // namespace SURELOG

#endif /* CONFIG_H */
