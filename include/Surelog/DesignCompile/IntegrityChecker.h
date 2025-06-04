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
 * File:   IntegrityChecker.h
 * Author: hs
 *
 * Created on August 10, 2024, 00:00 AM
 */

#ifndef SURELOG_INTEGRITYCHECKER_H
#define SURELOG_INTEGRITYCHECKER_H
#pragma once

#include <uhdm/UhdmListener.h>
#include <uhdm/uhdm_forward_decl.h>

#include <set>
#include <string_view>
#include <vector>

namespace SURELOG {
class Session;

class IntegrityChecker final : protected uhdm::UhdmListener {
 public:
  explicit IntegrityChecker(Session* session);

  void check(const uhdm::Design* const object);
  void check(const std::vector<const uhdm::Design*>& objects);

 private:
  bool isBuiltInPackageOnStack(const uhdm::Any* const object) const;
  bool isUVMMember(const uhdm::Any* const object) const;

  std::set<const uhdm::PreprocMacroInstance*> getMacroInstances(
      const uhdm::Any* const object) const;

  void populateAnyMacroInstanceCache(const uhdm::PreprocMacroInstance *const pmi);
  void populateAnyMacroInstanceCache();

  enum class LineColumnRelation {
    Before,
    Inside,
    After,
    Inconclusive,
  };

  std::string_view toString(LineColumnRelation relation) const;

  LineColumnRelation getLineColumnRelation(uint32_t sl, uint16_t sc,
                                           uint32_t el, uint16_t ec) const;

  LineColumnRelation getLineColumnRelation(uint32_t l, uint16_t c, uint32_t sl,
                                           uint16_t sc, uint32_t el,
                                           uint16_t ec) const;

  LineColumnRelation getLineColumnRelation(uint32_t csl, uint16_t csc,
                                           uint32_t cel, uint16_t cec,
                                           uint32_t psl, uint16_t psc,
                                           uint32_t pel, uint16_t pec) const;

  template <typename T>
  void reportDuplicates(const uhdm::Any* const object,
                        const std::vector<T*>& collection,
                        uint32_t vpiRelation) const;

  void reportInvalidLocation(const uhdm::Any* const object) const;

  void reportMissingLocation(const uhdm::Any* const object) const;

  static bool isImplicitFunctionReturnType(const uhdm::Any* const object);

  static std::string_view stripDecorations(std::string_view name);

  static bool areNamedSame(const uhdm::Any* const object,
                           const uhdm::Any* const actual);

  void reportInvalidNames(const uhdm::Any* const object) const;

  void reportInvalidFile(const uhdm::Any* const object) const;

  void reportNullActual(const uhdm::Any* const object) const;

  void enterAny(const uhdm::Any* const object, uint32_t vpiRelation) final;

  void enterAliasCollection(const uhdm::Any* const object,
                            const uhdm::AliasCollection& objects,
                            uint32_t vpiRelation) final;
  void enterAlwaysCollection(const uhdm::Any* const object,
                             const uhdm::AlwaysCollection& objects,
                             uint32_t vpiRelation) final;
  void enterAnyCollection(const uhdm::Any* const object,
                          const uhdm::AnyCollection& objects,
                          uint32_t vpiRelation) final;
  void enterAnyPatternCollection(const uhdm::Any* const object,
                                 const uhdm::AnyPatternCollection& objects,
                                 uint32_t vpiRelation) final;
  void enterArrayExprCollection(const uhdm::Any* const object,
                                const uhdm::ArrayExprCollection& objects,
                                uint32_t vpiRelation) final;
  void enterArrayNetCollection(const uhdm::Any* const object,
                               const uhdm::ArrayNetCollection& objects,
                               uint32_t vpiRelation) final;
  void enterArrayTypespecCollection(
      const uhdm::Any* const object,
      const uhdm::ArrayTypespecCollection& objects, uint32_t vpiRelation) final;
  void enterArrayVarCollection(const uhdm::Any* const object,
                               const uhdm::ArrayVarCollection& objects,
                               uint32_t vpiRelation) final;
  void enterAssertCollection(const uhdm::Any* const object,
                             const uhdm::AssertCollection& objects,
                             uint32_t vpiRelation) final;
  void enterAssignStmtCollection(const uhdm::Any* const object,
                                 const uhdm::AssignStmtCollection& objects,
                                 uint32_t vpiRelation) final;
  void enterAssignmentCollection(const uhdm::Any* const object,
                                 const uhdm::AssignmentCollection& objects,
                                 uint32_t vpiRelation) final;
  void enterAssumeCollection(const uhdm::Any* const object,
                             const uhdm::AssumeCollection& objects,
                             uint32_t vpiRelation) final;
  void enterAtomicStmtCollection(const uhdm::Any* const object,
                                 const uhdm::AtomicStmtCollection& objects,
                                 uint32_t vpiRelation) final;
  void enterAttributeCollection(const uhdm::Any* const object,
                                const uhdm::AttributeCollection& objects,
                                uint32_t vpiRelation) final;
  void enterBeginCollection(const uhdm::Any* const object,
                            const uhdm::BeginCollection& objects,
                            uint32_t vpiRelation) final;
  void enterBitSelectCollection(const uhdm::Any* const object,
                                const uhdm::BitSelectCollection& objects,
                                uint32_t vpiRelation) final;
  void enterBitTypespecCollection(const uhdm::Any* const object,
                                  const uhdm::BitTypespecCollection& objects,
                                  uint32_t vpiRelation) final;
  void enterBitVarCollection(const uhdm::Any* const object,
                             const uhdm::BitVarCollection& objects,
                             uint32_t vpiRelation) final;
  void enterBreakStmtCollection(const uhdm::Any* const object,
                                const uhdm::BreakStmtCollection& objects,
                                uint32_t vpiRelation) final;
  void enterByteTypespecCollection(const uhdm::Any* const object,
                                   const uhdm::ByteTypespecCollection& objects,
                                   uint32_t vpiRelation) final;
  void enterByteVarCollection(const uhdm::Any* const object,
                              const uhdm::ByteVarCollection& objects,
                              uint32_t vpiRelation) final;
  void enterCaseItemCollection(const uhdm::Any* const object,
                               const uhdm::CaseItemCollection& objects,
                               uint32_t vpiRelation) final;
  void enterCasePropertyCollection(const uhdm::Any* const object,
                                   const uhdm::CasePropertyCollection& objects,
                                   uint32_t vpiRelation) final;
  void enterCasePropertyItemCollection(
      const uhdm::Any* const object,
      const uhdm::CasePropertyItemCollection& objects,
      uint32_t vpiRelation) final;
  void enterCaseStmtCollection(const uhdm::Any* const object,
                               const uhdm::CaseStmtCollection& objects,
                               uint32_t vpiRelation) final;
  void enterChandleTypespecCollection(
      const uhdm::Any* const object,
      const uhdm::ChandleTypespecCollection& objects,
      uint32_t vpiRelation) final;
  void enterChandleVarCollection(const uhdm::Any* const object,
                                 const uhdm::ChandleVarCollection& objects,
                                 uint32_t vpiRelation) final;
  void enterCheckerDeclCollection(const uhdm::Any* const object,
                                  const uhdm::CheckerDeclCollection& objects,
                                  uint32_t vpiRelation) final;
  void enterCheckerInstCollection(const uhdm::Any* const object,
                                  const uhdm::CheckerInstCollection& objects,
                                  uint32_t vpiRelation) final;
  void enterCheckerInstPortCollection(
      const uhdm::Any* const object,
      const uhdm::CheckerInstPortCollection& objects,
      uint32_t vpiRelation) final;
  void enterCheckerPortCollection(const uhdm::Any* const object,
                                  const uhdm::CheckerPortCollection& objects,
                                  uint32_t vpiRelation) final;
  void enterClassDefnCollection(const uhdm::Any* const object,
                                const uhdm::ClassDefnCollection& objects,
                                uint32_t vpiRelation) final;
  void enterClassObjCollection(const uhdm::Any* const object,
                               const uhdm::ClassObjCollection& objects,
                               uint32_t vpiRelation) final;
  void enterClassTypespecCollection(
      const uhdm::Any* const object,
      const uhdm::ClassTypespecCollection& objects, uint32_t vpiRelation) final;
  void enterClassVarCollection(const uhdm::Any* const object,
                               const uhdm::ClassVarCollection& objects,
                               uint32_t vpiRelation) final;
  void enterClockedPropertyCollection(
      const uhdm::Any* const object,
      const uhdm::ClockedPropertyCollection& objects,
      uint32_t vpiRelation) final;
  void enterClockedSeqCollection(const uhdm::Any* const object,
                                 const uhdm::ClockedSeqCollection& objects,
                                 uint32_t vpiRelation) final;
  void enterClockingBlockCollection(
      const uhdm::Any* const object,
      const uhdm::ClockingBlockCollection& objects, uint32_t vpiRelation) final;
  void enterClockingIODeclCollection(
      const uhdm::Any* const object,
      const uhdm::ClockingIODeclCollection& objects,
      uint32_t vpiRelation) final;
  void enterConcurrentAssertionsCollection(
      const uhdm::Any* const object,
      const uhdm::ConcurrentAssertionsCollection& objects,
      uint32_t vpiRelation) final;
  void enterConstantCollection(const uhdm::Any* const object,
                               const uhdm::ConstantCollection& objects,
                               uint32_t vpiRelation) final;
  void enterConstrForeachCollection(
      const uhdm::Any* const object,
      const uhdm::ConstrForeachCollection& objects, uint32_t vpiRelation) final;
  void enterConstrIfCollection(const uhdm::Any* const object,
                               const uhdm::ConstrIfCollection& objects,
                               uint32_t vpiRelation) final;
  void enterConstrIfElseCollection(const uhdm::Any* const object,
                                   const uhdm::ConstrIfElseCollection& objects,
                                   uint32_t vpiRelation) final;
  void enterConstraintCollection(const uhdm::Any* const object,
                                 const uhdm::ConstraintCollection& objects,
                                 uint32_t vpiRelation) final;
  void enterConstraintExprCollection(
      const uhdm::Any* const object,
      const uhdm::ConstraintExprCollection& objects,
      uint32_t vpiRelation) final;
  void enterConstraintOrderingCollection(
      const uhdm::Any* const object,
      const uhdm::ConstraintOrderingCollection& objects,
      uint32_t vpiRelation) final;
  void enterContAssignBitCollection(
      const uhdm::Any* const object,
      const uhdm::ContAssignBitCollection& objects, uint32_t vpiRelation) final;
  void enterContAssignCollection(const uhdm::Any* const object,
                                 const uhdm::ContAssignCollection& objects,
                                 uint32_t vpiRelation) final;
  void enterContinueStmtCollection(const uhdm::Any* const object,
                                   const uhdm::ContinueStmtCollection& objects,
                                   uint32_t vpiRelation) final;
  void enterCoverCollection(const uhdm::Any* const object,
                            const uhdm::CoverCollection& objects,
                            uint32_t vpiRelation) final;
  void enterDeassignCollection(const uhdm::Any* const object,
                               const uhdm::DeassignCollection& objects,
                               uint32_t vpiRelation) final;
  void enterDefParamCollection(const uhdm::Any* const object,
                               const uhdm::DefParamCollection& objects,
                               uint32_t vpiRelation) final;
  void enterDelayControlCollection(const uhdm::Any* const object,
                                   const uhdm::DelayControlCollection& objects,
                                   uint32_t vpiRelation) final;
  void enterDelayTermCollection(const uhdm::Any* const object,
                                const uhdm::DelayTermCollection& objects,
                                uint32_t vpiRelation) final;
  void enterDesignCollection(const uhdm::Any* const object,
                             const uhdm::DesignCollection& objects,
                             uint32_t vpiRelation) final;
  void enterDisableCollection(const uhdm::Any* const object,
                              const uhdm::DisableCollection& objects,
                              uint32_t vpiRelation) final;
  void enterDisableForkCollection(const uhdm::Any* const object,
                                  const uhdm::DisableForkCollection& objects,
                                  uint32_t vpiRelation) final;
  void enterDisablesCollection(const uhdm::Any* const object,
                               const uhdm::DisablesCollection& objects,
                               uint32_t vpiRelation) final;
  void enterDistItemCollection(const uhdm::Any* const object,
                               const uhdm::DistItemCollection& objects,
                               uint32_t vpiRelation) final;
  void enterDistributionCollection(const uhdm::Any* const object,
                                   const uhdm::DistributionCollection& objects,
                                   uint32_t vpiRelation) final;
  void enterDoWhileCollection(const uhdm::Any* const object,
                              const uhdm::DoWhileCollection& objects,
                              uint32_t vpiRelation) final;
  void enterEnumConstCollection(const uhdm::Any* const object,
                                const uhdm::EnumConstCollection& objects,
                                uint32_t vpiRelation) final;
  void enterEnumNetCollection(const uhdm::Any* const object,
                              const uhdm::EnumNetCollection& objects,
                              uint32_t vpiRelation) final;
  void enterEnumTypespecCollection(const uhdm::Any* const object,
                                   const uhdm::EnumTypespecCollection& objects,
                                   uint32_t vpiRelation) final;
  void enterEnumVarCollection(const uhdm::Any* const object,
                              const uhdm::EnumVarCollection& objects,
                              uint32_t vpiRelation) final;
  void enterEventControlCollection(const uhdm::Any* const object,
                                   const uhdm::EventControlCollection& objects,
                                   uint32_t vpiRelation) final;
  void enterEventStmtCollection(const uhdm::Any* const object,
                                const uhdm::EventStmtCollection& objects,
                                uint32_t vpiRelation) final;
  void enterEventTypespecCollection(
      const uhdm::Any* const object,
      const uhdm::EventTypespecCollection& objects, uint32_t vpiRelation) final;
  void enterExpectStmtCollection(const uhdm::Any* const object,
                                 const uhdm::ExpectStmtCollection& objects,
                                 uint32_t vpiRelation) final;
  void enterExprCollection(const uhdm::Any* const object,
                           const uhdm::ExprCollection& objects,
                           uint32_t vpiRelation) final;
  void enterExtendsCollection(const uhdm::Any* const object,
                              const uhdm::ExtendsCollection& objects,
                              uint32_t vpiRelation) final;
  void enterFinalStmtCollection(const uhdm::Any* const object,
                                const uhdm::FinalStmtCollection& objects,
                                uint32_t vpiRelation) final;
  void enterForStmtCollection(const uhdm::Any* const object,
                              const uhdm::ForStmtCollection& objects,
                              uint32_t vpiRelation) final;
  void enterForceCollection(const uhdm::Any* const object,
                            const uhdm::ForceCollection& objects,
                            uint32_t vpiRelation) final;
  void enterForeachStmtCollection(const uhdm::Any* const object,
                                  const uhdm::ForeachStmtCollection& objects,
                                  uint32_t vpiRelation) final;
  void enterForeverStmtCollection(const uhdm::Any* const object,
                                  const uhdm::ForeverStmtCollection& objects,
                                  uint32_t vpiRelation) final;
  void enterForkStmtCollection(const uhdm::Any* const object,
                               const uhdm::ForkStmtCollection& objects,
                               uint32_t vpiRelation) final;
  void enterFuncCallCollection(const uhdm::Any* const object,
                               const uhdm::FuncCallCollection& objects,
                               uint32_t vpiRelation) final;
  void enterFunctionCollection(const uhdm::Any* const object,
                               const uhdm::FunctionCollection& objects,
                               uint32_t vpiRelation) final;
  void enterFunctionDeclCollection(const uhdm::Any* const object,
                                   const uhdm::FunctionDeclCollection& objects,
                                   uint32_t vpiRelation) final;
  void enterGateArrayCollection(const uhdm::Any* const object,
                                const uhdm::GateArrayCollection& objects,
                                uint32_t vpiRelation) final;
  void enterGateCollection(const uhdm::Any* const object,
                           const uhdm::GateCollection& objects,
                           uint32_t vpiRelation) final;
  void enterGenCaseCollection(const uhdm::Any* const object,
                              const uhdm::GenCaseCollection& objects,
                              uint32_t vpiRelation) final;
  void enterGenForCollection(const uhdm::Any* const object,
                             const uhdm::GenForCollection& objects,
                             uint32_t vpiRelation) final;
  void enterGenIfCollection(const uhdm::Any* const object,
                            const uhdm::GenIfCollection& objects,
                            uint32_t vpiRelation) final;
  void enterGenIfElseCollection(const uhdm::Any* const object,
                                const uhdm::GenIfElseCollection& objects,
                                uint32_t vpiRelation) final;
  void enterGenRegionCollection(const uhdm::Any* const object,
                                const uhdm::GenRegionCollection& objects,
                                uint32_t vpiRelation) final;
  void enterGenScopeArrayCollection(
      const uhdm::Any* const object,
      const uhdm::GenScopeArrayCollection& objects, uint32_t vpiRelation) final;
  void enterGenScopeCollection(const uhdm::Any* const object,
                               const uhdm::GenScopeCollection& objects,
                               uint32_t vpiRelation) final;
  void enterGenStmtCollection(const uhdm::Any* const object,
                              const uhdm::GenStmtCollection& objects,
                              uint32_t vpiRelation) final;
  void enterGenVarCollection(const uhdm::Any* const object,
                             const uhdm::GenVarCollection& objects,
                             uint32_t vpiRelation) final;
  void enterHierPathCollection(const uhdm::Any* const object,
                               const uhdm::HierPathCollection& objects,
                               uint32_t vpiRelation) final;
  void enterIODeclCollection(const uhdm::Any* const object,
                             const uhdm::IODeclCollection& objects,
                             uint32_t vpiRelation) final;
  void enterIfElseCollection(const uhdm::Any* const object,
                             const uhdm::IfElseCollection& objects,
                             uint32_t vpiRelation) final;
  void enterIfStmtCollection(const uhdm::Any* const object,
                             const uhdm::IfStmtCollection& objects,
                             uint32_t vpiRelation) final;
  void enterImmediateAssertCollection(
      const uhdm::Any* const object,
      const uhdm::ImmediateAssertCollection& objects,
      uint32_t vpiRelation) final;
  void enterImmediateAssumeCollection(
      const uhdm::Any* const object,
      const uhdm::ImmediateAssumeCollection& objects,
      uint32_t vpiRelation) final;
  void enterImmediateCoverCollection(
      const uhdm::Any* const object,
      const uhdm::ImmediateCoverCollection& objects,
      uint32_t vpiRelation) final;
  void enterImplicationCollection(const uhdm::Any* const object,
                                  const uhdm::ImplicationCollection& objects,
                                  uint32_t vpiRelation) final;
  void enterImportTypespecCollection(
      const uhdm::Any* const object,
      const uhdm::ImportTypespecCollection& objects,
      uint32_t vpiRelation) final;
  void enterIndexedPartSelectCollection(
      const uhdm::Any* const object,
      const uhdm::IndexedPartSelectCollection& objects,
      uint32_t vpiRelation) final;
  void enterInitialCollection(const uhdm::Any* const object,
                              const uhdm::InitialCollection& objects,
                              uint32_t vpiRelation) final;
  void enterInstanceArrayCollection(
      const uhdm::Any* const object,
      const uhdm::InstanceArrayCollection& objects, uint32_t vpiRelation) final;
  void enterInstanceCollection(const uhdm::Any* const object,
                               const uhdm::InstanceCollection& objects,
                               uint32_t vpiRelation) final;
  void enterIntTypespecCollection(const uhdm::Any* const object,
                                  const uhdm::IntTypespecCollection& objects,
                                  uint32_t vpiRelation) final;
  void enterIntVarCollection(const uhdm::Any* const object,
                             const uhdm::IntVarCollection& objects,
                             uint32_t vpiRelation) final;
  void enterIntegerNetCollection(const uhdm::Any* const object,
                                 const uhdm::IntegerNetCollection& objects,
                                 uint32_t vpiRelation) final;
  void enterIntegerTypespecCollection(
      const uhdm::Any* const object,
      const uhdm::IntegerTypespecCollection& objects,
      uint32_t vpiRelation) final;
  void enterIntegerVarCollection(const uhdm::Any* const object,
                                 const uhdm::IntegerVarCollection& objects,
                                 uint32_t vpiRelation) final;
  void enterInterfaceArrayCollection(
      const uhdm::Any* const object,
      const uhdm::InterfaceArrayCollection& objects,
      uint32_t vpiRelation) final;
  void enterInterfaceCollection(const uhdm::Any* const object,
                                const uhdm::InterfaceCollection& objects,
                                uint32_t vpiRelation) final;
  void enterInterfaceTFDeclCollection(
      const uhdm::Any* const object,
      const uhdm::InterfaceTFDeclCollection& objects,
      uint32_t vpiRelation) final;
  void enterInterfaceTypespecCollection(
      const uhdm::Any* const object,
      const uhdm::InterfaceTypespecCollection& objects,
      uint32_t vpiRelation) final;
  void enterLetDeclCollection(const uhdm::Any* const object,
                              const uhdm::LetDeclCollection& objects,
                              uint32_t vpiRelation) final;
  void enterLetExprCollection(const uhdm::Any* const object,
                              const uhdm::LetExprCollection& objects,
                              uint32_t vpiRelation) final;
  void enterLogicNetCollection(const uhdm::Any* const object,
                               const uhdm::LogicNetCollection& objects,
                               uint32_t vpiRelation) final;
  void enterLogicTypespecCollection(
      const uhdm::Any* const object,
      const uhdm::LogicTypespecCollection& objects, uint32_t vpiRelation) final;
  void enterLogicVarCollection(const uhdm::Any* const object,
                               const uhdm::LogicVarCollection& objects,
                               uint32_t vpiRelation) final;
  void enterLongIntTypespecCollection(
      const uhdm::Any* const object,
      const uhdm::LongIntTypespecCollection& objects,
      uint32_t vpiRelation) final;
  void enterLongIntVarCollection(const uhdm::Any* const object,
                                 const uhdm::LongIntVarCollection& objects,
                                 uint32_t vpiRelation) final;
  void enterMethodFuncCallCollection(
      const uhdm::Any* const object,
      const uhdm::MethodFuncCallCollection& objects,
      uint32_t vpiRelation) final;
  void enterMethodTaskCallCollection(
      const uhdm::Any* const object,
      const uhdm::MethodTaskCallCollection& objects,
      uint32_t vpiRelation) final;
  void enterModPathCollection(const uhdm::Any* const object,
                              const uhdm::ModPathCollection& objects,
                              uint32_t vpiRelation) final;
  void enterModportCollection(const uhdm::Any* const object,
                              const uhdm::ModportCollection& objects,
                              uint32_t vpiRelation) final;
  void enterModuleArrayCollection(const uhdm::Any* const object,
                                  const uhdm::ModuleArrayCollection& objects,
                                  uint32_t vpiRelation) final;
  void enterModuleCollection(const uhdm::Any* const object,
                             const uhdm::ModuleCollection& objects,
                             uint32_t vpiRelation) final;
  void enterModuleTypespecCollection(
      const uhdm::Any* const object,
      const uhdm::ModuleTypespecCollection& objects,
      uint32_t vpiRelation) final;
  void enterMulticlockSequenceExprCollection(
      const uhdm::Any* const object,
      const uhdm::MulticlockSequenceExprCollection& objects,
      uint32_t vpiRelation) final;
  void enterNamedEventArrayCollection(
      const uhdm::Any* const object,
      const uhdm::NamedEventArrayCollection& objects,
      uint32_t vpiRelation) final;
  void enterNamedEventCollection(const uhdm::Any* const object,
                                 const uhdm::NamedEventCollection& objects,
                                 uint32_t vpiRelation) final;
  void enterNetBitCollection(const uhdm::Any* const object,
                             const uhdm::NetBitCollection& objects,
                             uint32_t vpiRelation) final;
  void enterNetCollection(const uhdm::Any* const object,
                          const uhdm::NetCollection& objects,
                          uint32_t vpiRelation) final;
  void enterNetDriversCollection(const uhdm::Any* const object,
                                 const uhdm::NetDriversCollection& objects,
                                 uint32_t vpiRelation) final;
  void enterNetLoadsCollection(const uhdm::Any* const object,
                               const uhdm::NetLoadsCollection& objects,
                               uint32_t vpiRelation) final;
  void enterNetsCollection(const uhdm::Any* const object,
                           const uhdm::NetsCollection& objects,
                           uint32_t vpiRelation) final;
  void enterNullStmtCollection(const uhdm::Any* const object,
                               const uhdm::NullStmtCollection& objects,
                               uint32_t vpiRelation) final;
  void enterOperationCollection(const uhdm::Any* const object,
                                const uhdm::OperationCollection& objects,
                                uint32_t vpiRelation) final;
  void enterOrderedWaitCollection(const uhdm::Any* const object,
                                  const uhdm::OrderedWaitCollection& objects,
                                  uint32_t vpiRelation) final;
  void enterPackageCollection(const uhdm::Any* const object,
                              const uhdm::PackageCollection& objects,
                              uint32_t vpiRelation) final;
  void enterPackedArrayNetCollection(
      const uhdm::Any* const object,
      const uhdm::PackedArrayNetCollection& objects,
      uint32_t vpiRelation) final;
  void enterPackedArrayTypespecCollection(
      const uhdm::Any* const object,
      const uhdm::PackedArrayTypespecCollection& objects,
      uint32_t vpiRelation) final;
  void enterPackedArrayVarCollection(
      const uhdm::Any* const object,
      const uhdm::PackedArrayVarCollection& objects,
      uint32_t vpiRelation) final;
  void enterParamAssignCollection(const uhdm::Any* const object,
                                  const uhdm::ParamAssignCollection& objects,
                                  uint32_t vpiRelation) final;
  void enterParameterCollection(const uhdm::Any* const object,
                                const uhdm::ParameterCollection& objects,
                                uint32_t vpiRelation) final;
  void enterPartSelectCollection(const uhdm::Any* const object,
                                 const uhdm::PartSelectCollection& objects,
                                 uint32_t vpiRelation) final;
  void enterPathTermCollection(const uhdm::Any* const object,
                               const uhdm::PathTermCollection& objects,
                               uint32_t vpiRelation) final;
  void enterPortBitCollection(const uhdm::Any* const object,
                              const uhdm::PortBitCollection& objects,
                              uint32_t vpiRelation) final;
  void enterPortCollection(const uhdm::Any* const object,
                           const uhdm::PortCollection& objects,
                           uint32_t vpiRelation) final;
  void enterPortsCollection(const uhdm::Any* const object,
                            const uhdm::PortsCollection& objects,
                            uint32_t vpiRelation) final;
  void enterPreprocMacroDefinitionCollection(
      const uhdm::Any* const object,
      const uhdm::PreprocMacroDefinitionCollection& objects,
      uint32_t vpiRelation) final;
  void enterPreprocMacroInstanceCollection(
      const uhdm::Any* const object,
      const uhdm::PreprocMacroInstanceCollection& objects,
      uint32_t vpiRelation) final;
  void enterPrimTermCollection(const uhdm::Any* const object,
                               const uhdm::PrimTermCollection& objects,
                               uint32_t vpiRelation) final;
  void enterPrimitiveArrayCollection(
      const uhdm::Any* const object,
      const uhdm::PrimitiveArrayCollection& objects,
      uint32_t vpiRelation) final;
  void enterPrimitiveCollection(const uhdm::Any* const object,
                                const uhdm::PrimitiveCollection& objects,
                                uint32_t vpiRelation) final;
  void enterProcessCollection(const uhdm::Any* const object,
                              const uhdm::ProcessCollection& objects,
                              uint32_t vpiRelation) final;
  void enterProgramArrayCollection(const uhdm::Any* const object,
                                   const uhdm::ProgramArrayCollection& objects,
                                   uint32_t vpiRelation) final;
  void enterProgramCollection(const uhdm::Any* const object,
                              const uhdm::ProgramCollection& objects,
                              uint32_t vpiRelation) final;
  void enterPropFormalDeclCollection(
      const uhdm::Any* const object,
      const uhdm::PropFormalDeclCollection& objects,
      uint32_t vpiRelation) final;
  void enterPropertyDeclCollection(const uhdm::Any* const object,
                                   const uhdm::PropertyDeclCollection& objects,
                                   uint32_t vpiRelation) final;
  void enterPropertyInstCollection(const uhdm::Any* const object,
                                   const uhdm::PropertyInstCollection& objects,
                                   uint32_t vpiRelation) final;
  void enterPropertySpecCollection(const uhdm::Any* const object,
                                   const uhdm::PropertySpecCollection& objects,
                                   uint32_t vpiRelation) final;
  void enterPropertyTypespecCollection(
      const uhdm::Any* const object,
      const uhdm::PropertyTypespecCollection& objects,
      uint32_t vpiRelation) final;
  void enterRangeCollection(const uhdm::Any* const object,
                            const uhdm::RangeCollection& objects,
                            uint32_t vpiRelation) final;
  void enterRealTypespecCollection(const uhdm::Any* const object,
                                   const uhdm::RealTypespecCollection& objects,
                                   uint32_t vpiRelation) final;
  void enterRealVarCollection(const uhdm::Any* const object,
                              const uhdm::RealVarCollection& objects,
                              uint32_t vpiRelation) final;
  void enterRefModuleCollection(const uhdm::Any* const object,
                                const uhdm::RefModuleCollection& objects,
                                uint32_t vpiRelation) final;
  void enterRefObjCollection(const uhdm::Any* const object,
                             const uhdm::RefObjCollection& objects,
                             uint32_t vpiRelation) final;
  void enterRefTypespecCollection(const uhdm::Any* const object,
                                  const uhdm::RefTypespecCollection& objects,
                                  uint32_t vpiRelation) final;
  void enterRefVarCollection(const uhdm::Any* const object,
                             const uhdm::RefVarCollection& objects,
                             uint32_t vpiRelation) final;
  void enterRegArrayCollection(const uhdm::Any* const object,
                               const uhdm::RegArrayCollection& objects,
                               uint32_t vpiRelation) final;
  void enterRegCollection(const uhdm::Any* const object,
                          const uhdm::RegCollection& objects,
                          uint32_t vpiRelation) final;
  void enterReleaseCollection(const uhdm::Any* const object,
                              const uhdm::ReleaseCollection& objects,
                              uint32_t vpiRelation) final;
  void enterRepeatCollection(const uhdm::Any* const object,
                             const uhdm::RepeatCollection& objects,
                             uint32_t vpiRelation) final;
  void enterRepeatControlCollection(
      const uhdm::Any* const object,
      const uhdm::RepeatControlCollection& objects, uint32_t vpiRelation) final;
  void enterRestrictCollection(const uhdm::Any* const object,
                               const uhdm::RestrictCollection& objects,
                               uint32_t vpiRelation) final;
  void enterReturnStmtCollection(const uhdm::Any* const object,
                                 const uhdm::ReturnStmtCollection& objects,
                                 uint32_t vpiRelation) final;
  void enterScopeCollection(const uhdm::Any* const object,
                            const uhdm::ScopeCollection& objects,
                            uint32_t vpiRelation) final;
  void enterSeqFormalDeclCollection(
      const uhdm::Any* const object,
      const uhdm::SeqFormalDeclCollection& objects, uint32_t vpiRelation) final;
  void enterSequenceDeclCollection(const uhdm::Any* const object,
                                   const uhdm::SequenceDeclCollection& objects,
                                   uint32_t vpiRelation) final;
  void enterSequenceInstCollection(const uhdm::Any* const object,
                                   const uhdm::SequenceInstCollection& objects,
                                   uint32_t vpiRelation) final;
  void enterSequenceTypespecCollection(
      const uhdm::Any* const object,
      const uhdm::SequenceTypespecCollection& objects,
      uint32_t vpiRelation) final;
  void enterShortIntTypespecCollection(
      const uhdm::Any* const object,
      const uhdm::ShortIntTypespecCollection& objects,
      uint32_t vpiRelation) final;
  void enterShortIntVarCollection(const uhdm::Any* const object,
                                  const uhdm::ShortIntVarCollection& objects,
                                  uint32_t vpiRelation) final;
  void enterShortRealTypespecCollection(
      const uhdm::Any* const object,
      const uhdm::ShortRealTypespecCollection& objects,
      uint32_t vpiRelation) final;
  void enterShortRealVarCollection(const uhdm::Any* const object,
                                   const uhdm::ShortRealVarCollection& objects,
                                   uint32_t vpiRelation) final;
  void enterSimpleExprCollection(const uhdm::Any* const object,
                                 const uhdm::SimpleExprCollection& objects,
                                 uint32_t vpiRelation) final;
  void enterSoftDisableCollection(const uhdm::Any* const object,
                                  const uhdm::SoftDisableCollection& objects,
                                  uint32_t vpiRelation) final;
  void enterSourceFileCollection(const uhdm::Any* const object,
                                 const uhdm::SourceFileCollection& objects,
                                 uint32_t vpiRelation) final;
  void enterSpecParamCollection(const uhdm::Any* const object,
                                const uhdm::SpecParamCollection& objects,
                                uint32_t vpiRelation) final;
  void enterStringTypespecCollection(
      const uhdm::Any* const object,
      const uhdm::StringTypespecCollection& objects,
      uint32_t vpiRelation) final;
  void enterStringVarCollection(const uhdm::Any* const object,
                                const uhdm::StringVarCollection& objects,
                                uint32_t vpiRelation) final;
  void enterStructNetCollection(const uhdm::Any* const object,
                                const uhdm::StructNetCollection& objects,
                                uint32_t vpiRelation) final;
  void enterStructPatternCollection(
      const uhdm::Any* const object,
      const uhdm::StructPatternCollection& objects, uint32_t vpiRelation) final;
  void enterStructTypespecCollection(
      const uhdm::Any* const object,
      const uhdm::StructTypespecCollection& objects,
      uint32_t vpiRelation) final;
  void enterStructVarCollection(const uhdm::Any* const object,
                                const uhdm::StructVarCollection& objects,
                                uint32_t vpiRelation) final;
  void enterSwitchArrayCollection(const uhdm::Any* const object,
                                  const uhdm::SwitchArrayCollection& objects,
                                  uint32_t vpiRelation) final;
  void enterSwitchTranCollection(const uhdm::Any* const object,
                                 const uhdm::SwitchTranCollection& objects,
                                 uint32_t vpiRelation) final;
  void enterSysFuncCallCollection(const uhdm::Any* const object,
                                  const uhdm::SysFuncCallCollection& objects,
                                  uint32_t vpiRelation) final;
  void enterSysTaskCallCollection(const uhdm::Any* const object,
                                  const uhdm::SysTaskCallCollection& objects,
                                  uint32_t vpiRelation) final;
  void enterTFCallCollection(const uhdm::Any* const object,
                             const uhdm::TFCallCollection& objects,
                             uint32_t vpiRelation) final;
  void enterTableEntryCollection(const uhdm::Any* const object,
                                 const uhdm::TableEntryCollection& objects,
                                 uint32_t vpiRelation) final;
  void enterTaggedPatternCollection(
      const uhdm::Any* const object,
      const uhdm::TaggedPatternCollection& objects, uint32_t vpiRelation) final;
  void enterTaskCallCollection(const uhdm::Any* const object,
                               const uhdm::TaskCallCollection& objects,
                               uint32_t vpiRelation) final;
  void enterTaskCollection(const uhdm::Any* const object,
                           const uhdm::TaskCollection& objects,
                           uint32_t vpiRelation) final;
  void enterTaskDeclCollection(const uhdm::Any* const object,
                               const uhdm::TaskDeclCollection& objects,
                               uint32_t vpiRelation) final;
  void enterTaskFuncCollection(const uhdm::Any* const object,
                               const uhdm::TaskFuncCollection& objects,
                               uint32_t vpiRelation) final;
  void enterTaskFuncDeclCollection(const uhdm::Any* const object,
                                   const uhdm::TaskFuncDeclCollection& objects,
                                   uint32_t vpiRelation) final;
  void enterTchkCollection(const uhdm::Any* const object,
                           const uhdm::TchkCollection& objects,
                           uint32_t vpiRelation) final;
  void enterTchkTermCollection(const uhdm::Any* const object,
                               const uhdm::TchkTermCollection& objects,
                               uint32_t vpiRelation) final;
  void enterThreadCollection(const uhdm::Any* const object,
                             const uhdm::ThreadCollection& objects,
                             uint32_t vpiRelation) final;
  void enterTimeNetCollection(const uhdm::Any* const object,
                              const uhdm::TimeNetCollection& objects,
                              uint32_t vpiRelation) final;
  void enterTimeTypespecCollection(const uhdm::Any* const object,
                                   const uhdm::TimeTypespecCollection& objects,
                                   uint32_t vpiRelation) final;
  void enterTimeVarCollection(const uhdm::Any* const object,
                              const uhdm::TimeVarCollection& objects,
                              uint32_t vpiRelation) final;
  void enterTypeParameterCollection(
      const uhdm::Any* const object,
      const uhdm::TypeParameterCollection& objects, uint32_t vpiRelation) final;
  void enterTypedefTypespecCollection(
      const uhdm::Any* const object,
      const uhdm::TypedefTypespecCollection& objects,
      uint32_t vpiRelation) final;
  void enterTypespecCollection(const uhdm::Any* const object,
                               const uhdm::TypespecCollection& objects,
                               uint32_t vpiRelation) final;
  void enterTypespecMemberCollection(
      const uhdm::Any* const object,
      const uhdm::TypespecMemberCollection& objects,
      uint32_t vpiRelation) final;
  void enterUdpArrayCollection(const uhdm::Any* const object,
                               const uhdm::UdpArrayCollection& objects,
                               uint32_t vpiRelation) final;
  void enterUdpCollection(const uhdm::Any* const object,
                          const uhdm::UdpCollection& objects,
                          uint32_t vpiRelation) final;
  void enterUdpDefnCollection(const uhdm::Any* const object,
                              const uhdm::UdpDefnCollection& objects,
                              uint32_t vpiRelation) final;
  void enterUnionTypespecCollection(
      const uhdm::Any* const object,
      const uhdm::UnionTypespecCollection& objects, uint32_t vpiRelation) final;
  void enterUnionVarCollection(const uhdm::Any* const object,
                               const uhdm::UnionVarCollection& objects,
                               uint32_t vpiRelation) final;
  void enterUnsupportedExprCollection(
      const uhdm::Any* const object,
      const uhdm::UnsupportedExprCollection& objects,
      uint32_t vpiRelation) final;
  void enterUnsupportedStmtCollection(
      const uhdm::Any* const object,
      const uhdm::UnsupportedStmtCollection& objects,
      uint32_t vpiRelation) final;
  void enterUnsupportedTypespecCollection(
      const uhdm::Any* const object,
      const uhdm::UnsupportedTypespecCollection& objects,
      uint32_t vpiRelation) final;
  void enterUserSystfCollection(const uhdm::Any* const object,
                                const uhdm::UserSystfCollection& objects,
                                uint32_t vpiRelation) final;
  void enterVarBitCollection(const uhdm::Any* const object,
                             const uhdm::VarBitCollection& objects,
                             uint32_t vpiRelation) final;
  void enterVarSelectCollection(const uhdm::Any* const object,
                                const uhdm::VarSelectCollection& objects,
                                uint32_t vpiRelation) final;
  void enterVariablesCollection(const uhdm::Any* const object,
                                const uhdm::VariablesCollection& objects,
                                uint32_t vpiRelation) final;
  void enterVirtualInterfaceVarCollection(
      const uhdm::Any* const object,
      const uhdm::VirtualInterfaceVarCollection& objects,
      uint32_t vpiRelation) final;
  void enterVoidTypespecCollection(const uhdm::Any* const object,
                                   const uhdm::VoidTypespecCollection& objects,
                                   uint32_t vpiRelation) final;
  void enterWaitForkCollection(const uhdm::Any* const object,
                               const uhdm::WaitForkCollection& objects,
                               uint32_t vpiRelation) final;
  void enterWaitStmtCollection(const uhdm::Any* const object,
                               const uhdm::WaitStmtCollection& objects,
                               uint32_t vpiRelation) final;
  void enterWaitsCollection(const uhdm::Any* const object,
                            const uhdm::WaitsCollection& objects,
                            uint32_t vpiRelation) final;
  void enterWhileStmtCollection(const uhdm::Any* const object,
                                const uhdm::WhileStmtCollection& objects,
                                uint32_t vpiRelation) final;

 private:
  Session* const m_session = nullptr;
  const uhdm::Design* m_design = nullptr;

  using uhdm_type_set_t = std::set<uhdm::UhdmType>;
  const uhdm_type_set_t m_acceptedUhdmTypesWithInvalidLocation;

  using any_macro_instance_map_t =
      std::multimap<const uhdm::Any*, const uhdm::PreprocMacroInstance*>;
  any_macro_instance_map_t m_anyMacroInstance;
};

};  // namespace SURELOG

#endif /* SURELOG_INTEGRITYCHECKER_H */
