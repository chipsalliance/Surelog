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
    SIMPLE_TYPEDEF,
    ATOMIC
  };


  DataType()
      : m_fileContent(NULL),
        m_id(0),
        m_name(""),
        m_definition(NULL),
        m_is_parameter(false) {}
  DataType(FileContent* fC, NodeId id, std::string name, VObjectType type,
           bool isParameter = false)
      : m_fileContent(fC),
        m_id(id),
        m_name(name),
        m_definition(NULL),
        m_type(type),
        m_is_parameter(isParameter) {}
  void init(FileContent* fC, NodeId id, std::string name, VObjectType type,
            bool isParameter = false) {
    m_fileContent = fC;
    m_id = id;
    m_name = name;
    m_type = type;
    m_is_parameter = isParameter;
  }
  virtual ~DataType();

  FileContent* getFileContent() { return m_fileContent; }

  NodeId getNodeId() { return m_id; }

  std::string getName() { return m_name; }

  void setDefinition(DataType* def) { m_definition = def; }

  DataType* getDefinition() { return m_definition; }

  DataType* getActual();

  Category getCategory();

  virtual VObjectType getType() { return m_type; }

  bool isCompatible(Value*);

  bool isInteger_type(VObjectType type);
  bool isInteger_atom_type(VObjectType type);
  bool isInteger_vector_type(VObjectType type);
  bool isNon_integer_type(VObjectType type);
  bool isNet_type(VObjectType type);
  bool isData_type(VObjectType type);
  bool isString_type(VObjectType type);
  bool isNumber(VObjectType type);

  bool isParameter() { return m_is_parameter; }

 protected:
  FileContent* m_fileContent;
  NodeId m_id;
  std::string m_name;
  DataType* m_definition;
  VObjectType m_type;
  bool m_is_parameter;
};

};  // namespace SURELOG

#endif /* DATATYPE_H */
