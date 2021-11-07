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

#include <string_view>

#include "Common/RTTI.h"
#include "SourceCompile/SymbolTable.h"
#include "SourceCompile/VObjectTypes.h"

namespace UHDM {
class typespec;
};

namespace SURELOG {
class FileContent;
class Value;

class DataType : public RTTI {
  SURELOG_IMPLEMENT_RTTI(DataType, RTTI)
 public:
  enum class Category {
    STRUCT,
    UNION,
    ENUM,
    SIMPLE_TYPEDEF,  // typedef int
    BUILTIN,         // int, logic
    CLASS,
    REF,  // points to actual definition
    PARAMETER,
    TYPEDEF,
    DUMMY,  // placeholder for later binding
  };

  DataType() {}
  DataType(const FileContent* fC, NodeId id, std::string_view name,
           VObjectType type, bool isParameter = false)
      : m_fileContent(fC),
        m_id(id),
        m_name(name),
        m_definition(NULL),
        m_type(type),
        m_is_parameter(isParameter) {}

  void init(const FileContent* fC, NodeId id, std::string name,
            VObjectType type, bool isParameter = false) {
    m_fileContent = fC;
    m_id = id;
    m_name = name;
    m_type = type;
    m_is_parameter = isParameter;
  }
  virtual ~DataType() {}

  const FileContent* getFileContent() const { return m_fileContent; }

  NodeId getNodeId() const { return m_id; }

  const std::string& getName() const { return m_name; }

  // TODO(const correctness): these are apparently set in later stages.
  // Figure out how this can be formulated better. For now:
  // make m_definition mutable.
  void setDefinition(const DataType* def) const { m_definition = def; }
  const DataType* getDefinition() const { return m_definition; }

  const DataType* getActual() const;

  Category getCategory() const { return m_category; }

  virtual VObjectType getType() const { return m_type; }

  bool isCompatible(const Value* value) const;
  bool isParameter() const { return m_is_parameter; }

  static bool isInteger_type(VObjectType type);
  static bool isInteger_atom_type(VObjectType type);
  static bool isInteger_vector_type(VObjectType type);
  static bool isNon_integer_type(VObjectType type);
  static bool isNet_type(VObjectType type);
  static bool isData_type(VObjectType type);
  static bool isString_type(VObjectType type);
  static bool isNumber(VObjectType type);

  virtual bool isNet() const { return false; }

  UHDM::typespec* getTypespec() const { return m_typespec; }
  void setTypespec(UHDM::typespec* typespec) { m_typespec = typespec; }

  UHDM::typespec* getUnpackedTypespec() const { return m_unpacked_typespec; }
  void setUnpackedTypespec(UHDM::typespec* typespec) {
    m_unpacked_typespec = typespec;
  }

 protected:
  const FileContent* m_fileContent = nullptr;
  NodeId m_id = 0;
  std::string m_name;
  mutable const DataType* m_definition = nullptr;
  VObjectType m_type;
  bool m_is_parameter = false;
  UHDM::typespec* m_typespec = nullptr;
  UHDM::typespec* m_unpacked_typespec = nullptr;
  Category m_category = Category::REF;
};

}  // namespace SURELOG
SURELOG_IMPLEMENT_RTTI_VIRTUAL_CAST_FUNCTIONS(datatype_cast, SURELOG::DataType)

#endif /* DATATYPE_H */
