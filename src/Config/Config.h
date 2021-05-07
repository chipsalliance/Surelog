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

#include <map>
#include <string>
#include <string_view>
#include <vector>

#include "Design/FileContent.h"
#include "SourceCompile/SymbolTable.h"

namespace SURELOG {

class UseClause {
 public:
  enum Type { UseLib, UseConfig, UseModule, UseParam };
  UseClause(Type type, std::string_view name, const FileContent* fC, NodeId id)
      : m_type(type),
        m_name(name),
        m_fileContent(fC),
        m_node(id),
        m_used(false) {}
  UseClause(Type type, const FileContent* fC, NodeId id)
      : m_type(type),
        m_name(""),
        m_fileContent(fC),
        m_node(id),
        m_used(false) {}
  UseClause(Type type, const std::vector<std::string>& libs,
            const FileContent* fC, NodeId id)
      : m_type(type),
        m_name(""),
        m_libs(libs),
        m_fileContent(fC),
        m_node(id),
        m_used(false) {}

  Type getType() const { return m_type; }
  const std::string& getName() const { return m_name; }
  const std::vector<std::string>& getLibs() const { return m_libs; }
  const FileContent* getFileContent() const { return m_fileContent; }
  NodeId getNodeId() const { return m_node; }

  void setUsed() { m_used = true; }
  bool isUsed() const { return m_used; }

 private:
  const Type m_type;
  const std::string m_name;
  const std::vector<std::string> m_libs;
  const FileContent* m_fileContent;
  const NodeId m_node;

  bool m_used;
};

class Config final {
 public:
  Config(std::string_view name, const FileContent* fC, NodeId nodeId)
      : m_name(name),
        m_fileContent(fC),
        m_nodeId(nodeId),
        m_used(false),
        m_isTopLevel(false) {}

  const std::string& getName() const { return m_name; }
  const FileContent* getFileContent() const { return m_fileContent; }

  NodeId getNodeId() const { return m_nodeId; }

  void setIsUsed() { m_used = true; }
  bool isUsed() const { return m_used; }

  void setDesignTop(std::string top) { m_designTop = top; }
  const std::string& getDesignTop() const { return m_designTop; }

  void setDesignLib(std::string lib) { m_designLib = lib; }
  const std::string& getDesignLib() const { return m_designLib; }

  void addDefaultLib(const std::string& lib) { m_defaultLibs.push_back(lib); }
  const std::vector<std::string>& getDefaultLibs() const {
    return m_defaultLibs;
  }

  void addInstanceUseClause(const std::string& instance, UseClause use);
  const std::map<std::string, UseClause>& getInstanceUseClauses() const {
    return m_instanceUseClauses;
  }
  UseClause* getInstanceUseClause(const std::string& instance);

  void addCellUseClause(const std::string& cell, UseClause use);
  const std::map<std::string, UseClause>& getCellUseClauses() const {
    return m_cellUseClauses;
  }
  UseClause* getCellUseClause(const std::string& cell);

  bool isTopLevel() const { return m_isTopLevel; }
  void setTopLevel(bool top) { m_isTopLevel = top; }

 private:
  std::string m_name;
  const FileContent* m_fileContent;
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
