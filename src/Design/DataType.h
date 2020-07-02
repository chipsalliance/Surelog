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
 * File:   DataType.h
 * Author: alain
 *
 * Created on June 14, 2018, 10:07 PM
 */

#ifndef DATATYPE_H
#define DATATYPE_H

namespace SURELOG {
class FileContent;
class Value;
class DataType {
 public:
  enum Category {
    STRUCT,
    UNION,
    ENUM,
    SIMPLE_TYPEDEF, // typedef int
    BUILTIN, // int, logic
    CLASS,
    REF, // points to actual definition
    PARAMETER,
    TYPEDEF
  };


  DataType()
      : m_fileContent(NULL),
        m_id(0),
        m_name(""),
        m_definition(NULL),
        m_is_parameter(false) {}
  DataType(const FileContent* fC, NodeId id, std::string name, VObjectType type,
           bool isParameter = false)
      : m_fileContent(fC),
        m_id(id),
        m_name(name),
        m_definition(NULL),
        m_type(type),
        m_is_parameter(isParameter) {}
  void init(const FileContent* fC, NodeId id, std::string name,
            VObjectType type,
            bool isParameter = false) {
    m_fileContent = fC;
    m_id = id;
    m_name = name;
    m_type = type;
    m_is_parameter = isParameter;
  }
  virtual ~DataType();

  const FileContent* getFileContent() const { return m_fileContent; }

  NodeId getNodeId() const { return m_id; }

  const std::string& getName() const { return m_name; }

  // TODO(const correctness): these are apparently set later. Right now make
  // m_definition mutable
  void setDefinition(const DataType* def) const { m_definition = def; }
  const DataType* getDefinition() const { return m_definition; }

  const DataType* getActual() const;

  virtual Category getCategory() const { return Category::REF; }

  virtual VObjectType getType() const { return m_type; }

  bool isCompatible(const Value* value) const;

  bool isInteger_type(VObjectType type) const;
  bool isInteger_atom_type(VObjectType type) const;
  bool isInteger_vector_type(VObjectType type) const;
  bool isNon_integer_type(VObjectType type) const;
  bool isNet_type(VObjectType type) const;
  bool isData_type(VObjectType type) const;
  bool isString_type(VObjectType type) const;
  bool isNumber(VObjectType type) const;

  bool isParameter() const { return m_is_parameter; }

 protected:
  const FileContent* m_fileContent;
  NodeId m_id;
  std::string m_name;
  mutable const DataType* m_definition;
  VObjectType m_type;
  bool m_is_parameter;
};

};  // namespace SURELOG

#endif /* DATATYPE_H */
