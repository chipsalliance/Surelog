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
 * File:   CompileStep.h
 * Author: alain
 *
 * Created on July 5, 2017, 10:44 PM
 */

#ifndef COMPILESTEP_H
#define COMPILESTEP_H
#include "Design/VObject.h"
namespace SURELOG {

class CompileStep {
 public:
  CompileStep();
  CompileStep(const CompileStep& orig);
  virtual ~CompileStep();

  virtual const VObject Object(NodeId index) const = 0;

  virtual NodeId UniqueId(NodeId index) = 0;

  virtual SymbolId Name(NodeId index) = 0;

  virtual NodeId Child(NodeId index) = 0;

  virtual NodeId Sibling(NodeId index) = 0;

  virtual NodeId Definition(NodeId index) const = 0;

  virtual NodeId Parent(NodeId index) = 0;

  virtual unsigned short Type(NodeId index) const = 0;

  virtual unsigned int Line(NodeId index) = 0;

  virtual std::string Symbol(SymbolId id) = 0;

  virtual NodeId sl_get(NodeId parent,
                        VObjectType type) = 0;  // Get first item of type

  virtual NodeId sl_parent(
      NodeId parent, VObjectType type) = 0;  // Get first parent item of type

  virtual NodeId sl_parent(NodeId parent, std::vector<VObjectType> types,
                           VObjectType& actualType) = 0;

  virtual std::vector<NodeId> sl_get_all(
      NodeId parent, VObjectType type) = 0;  // get all items of type

  virtual NodeId sl_collect(
      NodeId parent,
      VObjectType type) = 0;  // Recursively search for first item of type

  virtual std::vector<NodeId> sl_collect_all(
      NodeId parent,
      VObjectType type) = 0;  // Recursively search for all items of type

  virtual std::string SymName(NodeId index) = 0;

 private:
};

};  // namespace SURELOG

#endif /* COMPILESTEP_H */
