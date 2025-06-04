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
 * File:   ObjectBinder.h
 * Author: hs
 *
 * Created on August 10, 2024, 00:00 AM
 */

#ifndef SURELOG_OBJECTBINDER_H
#define SURELOG_OBJECTBINDER_H
#pragma once

#include <Surelog/SourceCompile/VObjectTypes.h>

// uhdm
#include <uhdm/UhdmListener.h>
#include <uhdm/uhdm_forward_decl.h>

#include <map>
#include <set>
#include <string_view>
#include <vector>

namespace uhdm {
class Serializer;
}  // namespace uhdm

namespace SURELOG {

class Session;
class ValuedComponentI;

class ObjectBinder final : protected uhdm::UhdmListener {
 private:
  typedef std::map<const ValuedComponentI*, uhdm::BaseClass*>
      ForwardComponentMap;
  typedef std::map<const uhdm::BaseClass*, const ValuedComponentI*>
      ReverseComponentMap;
  typedef std::vector<const uhdm::Design*> DesignStack;
  typedef std::vector<const uhdm::Package*> PackageStack;
  typedef std::vector<const uhdm::Any*> PrefixStack;
  typedef std::vector<std::tuple<const uhdm::Any*, const ValuedComponentI*>>
      Unbounded;
  typedef std::set<const uhdm::Any*> Searched;

  enum class RefType {
    Object,
    Typespec,
  };

 public:
  ObjectBinder(Session* session, const ForwardComponentMap& componentMap,
               uhdm::Serializer& serializer, bool muteStdout);

  void bind(const uhdm::Design* const object, bool report);
  void bind(const std::vector<const uhdm::Design*>& objects, bool report);

 private:
  void enterHierPath(const uhdm::HierPath* const object,
                     uint32_t vpiRelation) final;
  void leaveHierPath(const uhdm::HierPath* const object,
                     uint32_t vpiRelation) final;

  void enterBitSelect(const uhdm::BitSelect* const object,
                      uint32_t vpiRelation) final;
  void enterVarSelect(const uhdm::VarSelect* const object,
                      uint32_t vpiRelation) final;

  // void enterChandle_var(const uhdm::ChandleVar* const object) final;

  void enterIndexedPartSelect(const uhdm::IndexedPartSelect* const object,
                              uint32_t vpiRelation) final;

  void enterPartSelect(const uhdm::PartSelect* const object,
                       uint32_t vpiRelation) final;

  void enterRefModule(const uhdm::RefModule* const object,
                      uint32_t vpiRelation) final;

  void enterRefObj(const uhdm::RefObj* const object,
                   uint32_t vpiRelation) final;

  void enterRefTypespec(const uhdm::RefTypespec* const object,
                        uint32_t vpiRelation) final;

  void enterClassDefn(const uhdm::ClassDefn* const object,
                      uint32_t vpiRelation) final;

 private:
  bool areSimilarNames(std::string_view name1, std::string_view name2) const;
  bool areSimilarNames(const uhdm::Any* const object1,
                       std::string_view name2) const;
  bool areSimilarNames(const uhdm::Any* const object1,
                       const uhdm::Any* const object2) const;
  static bool isInElaboratedTree(const uhdm::Any* const object);

  VObjectType getDefaultNetType(const ValuedComponentI* component) const;
  const uhdm::Any* getPrefix(const uhdm::Any* const object);

  template <typename T>
  const T* getParent(const uhdm::Any* object) const;

  const uhdm::Package* getPackage(std::string_view name,
                                  const uhdm::Any* object) const;
  const uhdm::Module* getModule(std::string_view defname,
                                const uhdm::Any* object) const;
  const uhdm::Interface* getInterface(std::string_view defname,
                                      const uhdm::Any* object) const;

  const uhdm::ClassDefn* getClassDefn(
      const uhdm::ClassDefnCollection* const collection,
      std::string_view name) const;
  const uhdm::ClassDefn* getClassDefn(std::string_view name,
                                      const uhdm::Any* object) const;

  const uhdm::Any* findInTypespec(std::string_view name, RefType refType,
                                  const uhdm::Typespec* const scope);
  const uhdm::Any* findInRefTypespec(std::string_view name, RefType refType,
                                     const uhdm::RefTypespec* const scope);
  template <typename T>
  const uhdm::Any* findInCollection(std::string_view name, RefType refType,
                                    const std::vector<T*>* const collection,
                                    const uhdm::Any* const scope);
  const uhdm::Any* findInScope(std::string_view name, RefType refType,
                               const uhdm::Scope* const scope);
  const uhdm::Any* findInInstance(std::string_view name, RefType refType,
                                  const uhdm::Instance* const scope);
  const uhdm::Any* findInInterface(std::string_view name, RefType refType,
                                   const uhdm::Interface* const scope);
  const uhdm::Any* findInPackage(std::string_view name, RefType refType,
                                 const uhdm::Package* const scope);
  const uhdm::Any* findInUdpDefn(std::string_view name, RefType refType,
                                 const uhdm::UdpDefn* const scope);
  const uhdm::Any* findInProgram(std::string_view name, RefType refType,
                                 const uhdm::Program* const scope);
  const uhdm::Any* findInFunction(std::string_view name, RefType refType,
                                  const uhdm::Function* const scope);
  const uhdm::Any* findInTask(std::string_view name, RefType refType,
                              const uhdm::Task* const scope);
  const uhdm::Any* findInForStmt(std::string_view name, RefType refType,
                                 const uhdm::ForStmt* const scope);
  const uhdm::Any* findInForeachStmt(std::string_view name, RefType refType,
                                     const uhdm::ForeachStmt* const scope);
  template <typename T>
  const uhdm::Any* findInScope_sub(
      std::string_view name, RefType refType, const T* const scope,
      typename std::enable_if<
          std::is_same<uhdm::Begin, typename std::decay<T>::type>::value ||
          std::is_same<uhdm::ForkStmt,
                       typename std::decay<T>::type>::value>::type* = 0);
  const uhdm::Any* findInClassDefn(std::string_view name, RefType refType,
                                   const uhdm::ClassDefn* const scope);
  const uhdm::Any* findInModule(std::string_view name, RefType refType,
                                const uhdm::Module* const scope);
  const uhdm::Any* findInDesign(std::string_view name, RefType refType,
                                const uhdm::Design* const scope);

  const uhdm::Any* bindObject(const uhdm::Any* const object);
  const uhdm::Any* bindObjectInScope(std::string_view name,
                                     const uhdm::Any* const object,
                                     const uhdm::Any* const scope);

  void reportErrors();
  bool createDefaultNets();

 private:
  Session* const m_session = nullptr;
  const ForwardComponentMap& m_forwardComponentMap;
  uhdm::Serializer& m_serializer;
  const bool m_muteStdout = false;

  ReverseComponentMap m_reverseComponentMap;
  PrefixStack m_prefixStack;
  Unbounded m_unbounded;
  Searched m_searched;
};

};  // namespace SURELOG

#endif /* SURELOG_OBJECTBINDER_H */
