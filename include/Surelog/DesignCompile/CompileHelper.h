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
 * File:   CompileHelper.h
 * Author: alain
 *
 * Created on May 14, 2019, 8:03 PM
 */

#ifndef SURELOG_COMPILEHELPER_H
#define SURELOG_COMPILEHELPER_H
#pragma once

#include <Surelog/Common/PathId.h>
#include <Surelog/Common/RTTI.h>
#include <Surelog/Design/ValuedComponentI.h>
#include <Surelog/Expression/ExprBuilder.h>
#include <Surelog/SourceCompile/VObjectTypes.h>

#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

// UHDM
#include <uhdm/always.h>
#include <uhdm/array_var.h>
#include <uhdm/assignment.h>
#include <uhdm/atomic_stmt.h>
#include <uhdm/attribute.h>
#include <uhdm/clocking_block.h>
#include <uhdm/constant.h>
#include <uhdm/cont_assign.h>
#include <uhdm/containers.h>
#include <uhdm/event_control.h>
#include <uhdm/expr.h>
#include <uhdm/final_stmt.h>
#include <uhdm/function.h>
#include <uhdm/hier_path.h>
#include <uhdm/initial.h>
#include <uhdm/int_typespec.h>
#include <uhdm/io_decl.h>
#include <uhdm/method_func_call.h>
#include <uhdm/module.h>
#include <uhdm/module_array.h>
#include <uhdm/primitive.h>
#include <uhdm/property_decl.h>
#include <uhdm/range.h>
#include <uhdm/ref_module.h>
#include <uhdm/sequence_decl.h>
#include <uhdm/task_func.h>
#include <uhdm/typespec.h>
#include <uhdm/typespec_member.h>
#include <uhdm/uhdm_types.h>
#include <uhdm/variables.h>

namespace uhdm {
class constant;
class Serializer;
}  // namespace uhdm

namespace SURELOG {
class CompileDesign;
class DataType;
class Design;
class DesignComponent;
class FileContent;
class Function;
class NodeId;
class Parameter;
class Procedure;
class Scope;
class Session;
class Signal;
class Statement;
class Task;
class TfPortItem;
using TfPortList = std::vector<TfPortItem*>;

class FScope : public ValuedComponentI {
  SURELOG_IMPLEMENT_RTTI(FScope, ValuedComponentI)
 public:
  FScope(Session* session, const SURELOG::ValuedComponentI* parent,
         SURELOG::ValuedComponentI* definition)
      : ValuedComponentI(session, parent, definition) {}

 private:
};

using Scopes = std::vector<FScope*>;
enum class Elaborate : bool { Yes = true, No = false };
enum class Reduce : bool { Yes = true, No = false };

class CompileHelper final {
 public:
  explicit CompileHelper(Session* session);
  CompileHelper(const CompileHelper&) = delete;

  void setDesign(Design* design) { m_exprBuilder.setDesign(design); }

  // ------------------------------------------------------------------------------------------
  // Surelog internal modeling

  bool importPackage(DesignComponent* scope, Design* design,
                     const FileContent* fC, NodeId id,
                     CompileDesign* compileDesign, bool inPackage = false);

  bool compileTfPortList(Procedure* parent, const FileContent* fC, NodeId id,
                         TfPortList& targetList);

  const DataType* compileTypeDef(DesignComponent* scope, const FileContent* fC,
                                 NodeId id, CompileDesign* compileDesign,
                                 Reduce reduce, uhdm::Any* pstmt = nullptr);

  bool compileScopeBody(Scope* parent, Statement* parentStmt,
                        const FileContent* fC, NodeId id);

  bool compileScopeVariable(Scope* parent, const FileContent* fC, NodeId id);

  bool compileSubroutine_call(Scope* parent, Statement* parentStmt,
                              const FileContent* fC, NodeId id);

  bool compileSeqBlock_stmt(Scope* parent, Statement* parentStmt,
                            const FileContent* fC, NodeId id);

  bool compileLoop_stmt(Scope* parent, Statement* parentStmt,
                        const FileContent* fC, NodeId id);

  bool compileForLoop_stmt(Scope* parent, Statement* parentStmt,
                           const FileContent* fC, NodeId id);

  bool compileForeachLoop_stmt(Scope* parent, Statement* parentStmt,
                               const FileContent* fC, NodeId id);

  Function* compileFunctionPrototype(DesignComponent* scope,
                                     const FileContent* fC, NodeId id,
                                     CompileDesign* compileDesign);

  Task* compileTaskPrototype(DesignComponent* scope, const FileContent* fC,
                             NodeId id, CompileDesign* compileDesign);

  bool compilePortDeclaration(DesignComponent* scope, const FileContent* fC,
                              NodeId id, CompileDesign* compileDesign,
                              VObjectType& port_direction, bool hasNonNullPort);

  bool compileAnsiPortDeclaration(DesignComponent* component,
                                  const FileContent* fC, NodeId id,
                                  CompileDesign* compileDesign,
                                  VObjectType& port_direction);

  bool elaborationSystemTask(DesignComponent* component, const FileContent* fC,
                             NodeId id, CompileDesign* compileDesign);

  bool compileNetDeclaration(DesignComponent* component, const FileContent* fC,
                             NodeId id, bool interface,
                             CompileDesign* compileDesign,
                             uhdm::AttributeCollection* attributes);

  bool compileDataDeclaration(DesignComponent* component, const FileContent* fC,
                              NodeId id, bool interface,
                              CompileDesign* compileDesign, Reduce reduce,
                              uhdm::AttributeCollection* attributes);

  bool compileSignal(DesignComponent* comp, CompileDesign* compileDesign,
                     Signal* sig, std::string_view prefix, bool signalIsPort,
                     Reduce reduce);

  uhdm::Typespec* compileTypeParameter(DesignComponent* component,
                                       CompileDesign* compileDesign,
                                       Parameter* sit);

  // ------------------------------------------------------------------------------------------
  // UHDM modeling

  std::vector<uhdm::ContAssign*> compileContinuousAssignment(
      DesignComponent* component, const FileContent* fC, NodeId id,
      CompileDesign* compileDesign, uhdm::Any* pstmt,
      ValuedComponentI* instance);

  uhdm::Always* compileAlwaysBlock(DesignComponent* component,
                                   const FileContent* fC, NodeId id,
                                   CompileDesign* compileDesign,
                                   uhdm::Any* pstmt,
                                   ValuedComponentI* instance);

  uhdm::Any* compileTfCall(DesignComponent* component, const FileContent* fC,
                           NodeId Tf_call_stmt, CompileDesign* compileDesign,
                           uhdm::Any* pexpr);

  uhdm::AnyCollection* compileTfCallArguments(
      DesignComponent* component, const FileContent* fC, NodeId Arg_list_node,
      CompileDesign* compileDesign, Reduce reduce, uhdm::Any* call,
      ValuedComponentI* instance, bool muteErrors);

  uhdm::Assignment* compileBlockingAssignment(
      DesignComponent* component, const FileContent* fC, NodeId nodeId,
      bool blocking, CompileDesign* compileDesign, uhdm::Any* pstmt,
      ValuedComponentI* instance = nullptr);

  uhdm::AtomicStmt* compileProceduralTimingControlStmt(
      DesignComponent* component, const FileContent* fC, NodeId nodeId,
      CompileDesign* compileDesign, uhdm::Any* pstmt,
      ValuedComponentI* instance = nullptr);

  uhdm::AtomicStmt* compileEventControlStmt(
      DesignComponent* component, const FileContent* fC, NodeId nodeId,
      CompileDesign* compileDesign, uhdm::Any* pstmt,
      ValuedComponentI* instance = nullptr, bool muteErrors = false);

  uhdm::AtomicStmt* compileConditionalStmt(DesignComponent* component,
                                           const FileContent* fC, NodeId nodeId,
                                           CompileDesign* compileDesign,
                                           uhdm::Any* pstmt,
                                           ValuedComponentI* instance = nullptr,
                                           bool muteErrors = false);

  bool compileParameterDeclaration(DesignComponent* component,
                                   const FileContent* fC, NodeId nodeId,
                                   CompileDesign* compileDesign, Reduce reduce,
                                   bool localParam,
                                   ValuedComponentI* m_instance,
                                   bool port_param, bool muteErrors);

  NodeId setFuncTaskQualifiers(const FileContent* fC, NodeId nodeId,
                               uhdm::TaskFunc* tf);
  NodeId setFuncTaskDeclQualifiers(const FileContent* fC, NodeId nodeId,
                                   uhdm::TaskFuncDecl* tfd);

  bool compileTask(DesignComponent* component, const FileContent* fC,
                   NodeId nodeId, CompileDesign* compileDesign, Reduce reduce,
                   ValuedComponentI* instance, bool isMethod);

  bool compileFunction(DesignComponent* component, const FileContent* fC,
                       NodeId nodeId, CompileDesign* compileDesign,
                       Reduce reduce, ValuedComponentI* instance,
                       bool isMethod);

  bool compileAssertionItem(DesignComponent* component, const FileContent* fC,
                            NodeId nodeId, CompileDesign* compileDesign);

  std::vector<uhdm::IODecl*>* compileTfPortList(DesignComponent* scope,
                                                uhdm::Any* parent,
                                                const FileContent* fC,
                                                NodeId id,
                                                CompileDesign* compileDesign);

  template <typename T>
  std::pair<std::vector<uhdm::IODecl*>*, std::vector<uhdm::Variables*>*>
  compileTfPortDecl(DesignComponent* scope, T* parent, const FileContent* fC,
                    NodeId id, CompileDesign* compileDesign);

  uhdm::AtomicStmt* compileCaseStmt(DesignComponent* component,
                                    const FileContent* fC, NodeId nodeId,
                                    CompileDesign* compileDesign,
                                    uhdm::Any* pstmt = nullptr,
                                    ValuedComponentI* instance = nullptr,
                                    bool muteErrors = false);
  uhdm::AtomicStmt* compileRandcaseStmt(DesignComponent* component,
                                        const FileContent* fC, NodeId nodeId,
                                        CompileDesign* compileDesign,
                                        uhdm::Any* pstmt = nullptr,
                                        ValuedComponentI* instance = nullptr,
                                        bool muteErrors = false);

  uhdm::AnyCollection* compileStmt(DesignComponent* component,
                                   const FileContent* fC, NodeId nodeId,
                                   CompileDesign* compileDesign, Reduce reduce,
                                   uhdm::Any* pstmt = nullptr,
                                   ValuedComponentI* instance = nullptr,
                                   bool muteError = false);

  uhdm::Any* compileVariable(DesignComponent* component, const FileContent* fC,
                             NodeId declarationId, NodeId nameId,
                             CompileDesign* compileDesign, Reduce reduce,
                             uhdm::Any* pstmt, ValuedComponentI* instance,
                             bool muteErrors);
  uhdm::Any* compileVariable(DesignComponent* component,
                             CompileDesign* compileDesign, Signal* sig,
                             std::vector<uhdm::Range*>* packedDimensions,
                             int32_t packedSize,
                             std::vector<uhdm::Range*>* unpackedDimensions,
                             int32_t unpackedSize, uhdm::Expr* assignExp,
                             uhdm::Typespec* tps);

  uhdm::Typespec* compileTypespec(DesignComponent* component,
                                  const FileContent* fC, NodeId nodeId,
                                  CompileDesign* compileDesign, Reduce reduce,
                                  uhdm::Any* pstmt, ValuedComponentI* instance,
                                  bool isVariable);

  uhdm::Typespec* compileBuiltinTypespec(DesignComponent* component,
                                         const FileContent* fC, NodeId type,
                                         VObjectType the_type,
                                         CompileDesign* compileDesign,
                                         std::vector<uhdm::Range*>* ranges,
                                         uhdm::Any* pstmt);

  uhdm::Typespec* compileDatastructureTypespec(
      DesignComponent* component, const FileContent* fC, NodeId type,
      CompileDesign* compileDesign, Reduce reduce,
      SURELOG::ValuedComponentI* instance, std::string_view suffixname = "",
      std::string_view typeName = "");

  uhdm::Any* compileCheckerInstantiation(DesignComponent* component,
                                         const FileContent* fC, NodeId nodeId,
                                         CompileDesign* compileDesign,
                                         uhdm::Any* pstmt,
                                         ValuedComponentI* instance);

  uhdm::Any* compileSimpleImmediateAssertion(DesignComponent* component,
                                             const FileContent* fC,
                                             NodeId nodeId,
                                             CompileDesign* compileDesign,
                                             uhdm::Any* pstmt,
                                             ValuedComponentI* instance);

  uhdm::Any* compileDeferredImmediateAssertion(DesignComponent* component,
                                               const FileContent* fC,
                                               NodeId nodeId,
                                               CompileDesign* compileDesign,
                                               uhdm::Any* pstmt,
                                               ValuedComponentI* instance);

  uhdm::Any* compileConcurrentAssertion(DesignComponent* component,
                                        const FileContent* fC, NodeId nodeId,
                                        CompileDesign* compileDesign,
                                        uhdm::Any* pstmt,
                                        ValuedComponentI* instance);

  uhdm::PropertyDecl* compilePropertyDeclaration(DesignComponent* component,
                                                 const FileContent* fC,
                                                 NodeId nodeId,
                                                 CompileDesign* compileDesign,
                                                 uhdm::Any* pstmt,
                                                 ValuedComponentI* instance);

  uhdm::SequenceDecl* compileSequenceDeclaration(DesignComponent* component,
                                                 const FileContent* fC,
                                                 NodeId nodeId,
                                                 CompileDesign* compileDesign,
                                                 uhdm::Any* pstmt,
                                                 ValuedComponentI* instance);

  uhdm::Initial* compileInitialBlock(DesignComponent* component,
                                     const FileContent* fC, NodeId id,
                                     CompileDesign* compileDesign,
                                     uhdm::Any* pstmt);

  uhdm::FinalStmt* compileFinalBlock(DesignComponent* component,
                                     const FileContent* fC, NodeId id,
                                     CompileDesign* compileDesign,
                                     uhdm::Any* pstmt);

  void compileBindStmt(DesignComponent* component, const FileContent* fC,
                       NodeId nodeId, CompileDesign* compileDesign,
                       ValuedComponentI* instance = nullptr);

  uhdm::Constant* constantFromValue(Value* val, CompileDesign* compileDesign);

  uhdm::Any* compileExpression(DesignComponent* component,
                               const FileContent* fC, NodeId nodeId,
                               CompileDesign* compileDesign, Reduce reduce,
                               uhdm::Any* pexpr = nullptr,
                               ValuedComponentI* instance = nullptr,
                               bool muteErrors = false);

  uhdm::Any* compilePartSelectRange(
      DesignComponent* component, const FileContent* fC, NodeId Constant_range,
      std::string_view name, CompileDesign* compileDesign, Reduce reduce,
      uhdm::Any* pexpr, ValuedComponentI* instance, bool muteErrors);

  uhdm::RangeCollection* compileRanges(DesignComponent* component,
                                       const FileContent* fC,
                                       NodeId Packed_dimension,
                                       CompileDesign* compileDesign,
                                       Reduce reduce, uhdm::Any* pexpr,
                                       ValuedComponentI* instance,
                                       int32_t& size, bool muteErrors);

  uhdm::Any* compileAssignmentPattern(DesignComponent* component,
                                      const FileContent* fC,
                                      NodeId Assignment_pattern,
                                      CompileDesign* compileDesign,
                                      Reduce reduce, uhdm::Any* pexpr,
                                      ValuedComponentI* instance);

  uhdm::ArrayVar* compileArrayVar(DesignComponent* component,
                                  const FileContent* fC, NodeId varId,
                                  CompileDesign* compileDesign,
                                  uhdm::Any* pexpr, ValuedComponentI* instance);

  uhdm::Any* compileProceduralContinuousAssign(DesignComponent* component,
                                               const FileContent* fC,
                                               NodeId nodeId,
                                               CompileDesign* compileDesign);

  uhdm::AnyCollection* compileDataDeclaration(
      DesignComponent* component, const FileContent* fC, NodeId nodeId,
      CompileDesign* compileDesign, Reduce reduce, uhdm::Any* pstmt = nullptr,
      ValuedComponentI* instance = nullptr);

  uhdm::Any* compileForLoop(DesignComponent* component, const FileContent* fC,
                            NodeId nodeId, CompileDesign* compileDesign,
                            bool muteErrors = false);

  uhdm::Any* compileSelectExpression(
      DesignComponent* component, const FileContent* fC, NodeId Bit_select,
      std::string_view name, CompileDesign* compileDesign, Reduce reduce,
      uhdm::Any* pexpr, ValuedComponentI* instance, bool muteErrors);

  uhdm::Any* compileBits(DesignComponent* component, const FileContent* fC,
                         NodeId Expression, CompileDesign* compileDesign,
                         Reduce reduce, uhdm::Any* pexpr,
                         ValuedComponentI* instance, bool sizeMode,
                         bool muteErrors);

  uhdm::Any* compileClog2(DesignComponent* component, const FileContent* fC,
                          NodeId Expression, CompileDesign* compileDesign,
                          Reduce reduce, uhdm::Any* pexpr,
                          ValuedComponentI* instance, bool muteErrors);

  uhdm::Any* compileBound(DesignComponent* component, const FileContent* fC,
                          NodeId Expression, CompileDesign* compileDesign,
                          Reduce reduce, uhdm::Any* pexpr,
                          ValuedComponentI* instance, bool muteErrors,
                          std::string_view name);

  uhdm::Any* compileTypename(DesignComponent* component, const FileContent* fC,
                             NodeId Expression, CompileDesign* compileDesign,
                             Reduce reduce, uhdm::Any* pexpr,
                             ValuedComponentI* instance);

  const uhdm::Typespec* getTypespec(DesignComponent* component,
                                    const FileContent* fC, NodeId id,
                                    CompileDesign* compileDesign, Reduce reduce,
                                    ValuedComponentI* instance);

  uhdm::Any* compileComplexFuncCall(DesignComponent* component,
                                    const FileContent* fC, NodeId nodeId,
                                    CompileDesign* compileDesign, Reduce reduce,
                                    uhdm::Any* pexpr,
                                    ValuedComponentI* instance,
                                    bool muteErrors);

  uhdm::AttributeCollection* compileAttributes(DesignComponent* component,
                                               const FileContent* fC,
                                               NodeId nodeId,
                                               CompileDesign* compileDesign,
                                               uhdm::Any* pexpr);

  void compileImportDeclaration(DesignComponent* component,
                                const FileContent* fC, NodeId id,
                                CompileDesign* compileDesign);

  uhdm::Any* bindVariable(DesignComponent* component, const uhdm::Any* scope,
                          std::string_view name, CompileDesign* compileDesign);

  uhdm::Any* bindVariable(DesignComponent* component,
                          ValuedComponentI* instance, std::string_view name,
                          CompileDesign* compileDesign);

  uhdm::Any* bindParameter(DesignComponent* component,
                           ValuedComponentI* instance, std::string_view name,
                           CompileDesign* compileDesign, bool crossHierarchy);

  uhdm::EventControl* compileClocking_event(DesignComponent* component,
                                            const FileContent* fC,
                                            NodeId nodeId,
                                            CompileDesign* compileDesign,
                                            uhdm::Any* pexpr,
                                            ValuedComponentI* instance);

  uhdm::ClockingBlock* compileClockingBlock(DesignComponent* component,
                                            const FileContent* fC,
                                            NodeId nodeId,
                                            CompileDesign* compileDesign,
                                            uhdm::Any* pexpr,
                                            ValuedComponentI* instance);

  uhdm::AtomicStmt* compileDelayControl(DesignComponent* component,
                                        const FileContent* fC,
                                        NodeId Procedural_timing_control,
                                        CompileDesign* compileDesign,
                                        uhdm::Any* pexpr,
                                        ValuedComponentI* instance);

  bool compileClassConstructorDeclaration(DesignComponent* component,
                                          const FileContent* fC, NodeId nodeId,
                                          CompileDesign* compileDesign);

  uhdm::MethodFuncCall* compileRandomizeCall(DesignComponent* component,
                                             const FileContent* fC,
                                             NodeId nodeId,
                                             CompileDesign* compileDesign,
                                             uhdm::Any* pexpr);

  uhdm::Any* compileConstraintBlock(DesignComponent* component,
                                    const FileContent* fC, NodeId nodeId,
                                    CompileDesign* compileDesign,
                                    uhdm::Any* pexpr);

  uint32_t getBuiltinType(VObjectType type);

  void compileLetDeclaration(DesignComponent* component, const FileContent* fC,
                             NodeId nodeId, CompileDesign* compileDesign);

  std::pair<std::vector<uhdm::ModuleArray*>, std::vector<uhdm::RefModule*>>
  compileInstantiation(ModuleDefinition* mod, const FileContent* fC,
                       CompileDesign* compileDesign, uhdm::Any* pexpr,
                       NodeId id, ValuedComponentI* instance);

  void writePrimTerms(ModuleDefinition* mod, const FileContent* fC,
                      CompileDesign* compileDesign, NodeId id,
                      uhdm::Primitive* prim, int32_t vpiGateType,
                      ValuedComponentI* instance);

  void compileUdpInstantiation(ModuleDefinition* mod, const FileContent* fC,
                               CompileDesign* compileDesign, NodeId id,
                               ValuedComponentI* instance);

  void compileGateInstantiation(ModuleDefinition* mod, const FileContent* fC,
                                CompileDesign* compileDesign, NodeId id,
                                ValuedComponentI* instance);

  void compileHighConn(ModuleDefinition* component, const FileContent* fC,
                       CompileDesign* compileDesign, NodeId id,
                       uhdm::PortCollection* ports, uhdm::Any* pexpr);

  uhdm::AnyCollection* compileGenStmt(DesignComponent* component,
                                      const FileContent* fC, NodeId id,
                                      CompileDesign* compileDesign);

  uhdm::AnyCollection* compileGenVars(DesignComponent* component,
                                      const FileContent* fC, NodeId id,
                                      CompileDesign* compileDesign);

  uhdm::Constant* compileConst(const FileContent* fC, NodeId child,
                               uhdm::Serializer& s);

  /** Variable is either a bit select or a uhdm::Range*/
  bool isSelected(const FileContent* fC, NodeId id);

  bool isMultidimensional(uhdm::Typespec* ts, DesignComponent* component);

  bool isDecreasingRange(uhdm::Typespec* ts, DesignComponent* component);

  uhdm::Expr* reduceExpr(uhdm::Any* expr, bool& invalidValue,
                         DesignComponent* component,
                         CompileDesign* compileDesign,
                         ValuedComponentI* instance, PathId fileId,
                         uint32_t lineNumber, uhdm::Any* pexpr,
                         bool muteErrors = false);

  int32_t adjustOpSize(const uhdm::Typespec* tps, uhdm::Expr* cop,
                       int32_t opIndex, uhdm::Expr* rhs,
                       DesignComponent* component, CompileDesign* compileDesign,
                       ValuedComponentI* instance);

  void adjustUnsized(uhdm::Constant* c, int32_t size);

  uhdm::Any* defaultPatternAssignment(const uhdm::Typespec* tps, uhdm::Any* exp,
                                      DesignComponent* component,
                                      CompileDesign* compileDesign,
                                      Reduce reduce,
                                      ValuedComponentI* instance);

  uhdm::Expr* expandPatternAssignment(
      const uhdm::Typespec* tps, uhdm::Expr* rhs, DesignComponent* component,
      CompileDesign* compileDesign, Reduce reduce, ValuedComponentI* instance);

  uint64_t Bits(const uhdm::Any* typespec, bool& invalidValue,
                DesignComponent* component, CompileDesign* compileDesign,
                Reduce reduce, ValuedComponentI* instance, PathId fileId,
                uint32_t lineNumber, bool sizeMode);

  uhdm::Variables* getSimpleVarFromTypespec(
      const FileContent* fC, NodeId declarationId, NodeId nameId,
      uhdm::Typespec* spec, std::vector<uhdm::Range*>* packedDimensions,
      CompileDesign* compileDesign);

  std::pair<uhdm::TaskFunc*, DesignComponent*> getTaskFunc(
      std::string_view name, DesignComponent* component,
      CompileDesign* compileDesign, ValuedComponentI* instance,
      uhdm::Any* pexpr);

  uhdm::Expr* EvalFunc(uhdm::Function* func, std::vector<uhdm::Any*>* args,
                       bool& invalidValue, DesignComponent* component,
                       CompileDesign* compileDesign, ValuedComponentI* instance,
                       PathId fileId, uint32_t lineNumber, uhdm::Any* pexpr);

  void evalScheduledExprs(DesignComponent* component,
                          CompileDesign* compileDesign);

  uhdm::Expr* exprFromAssign(DesignComponent* component,
                             CompileDesign* compileDesign,
                             const FileContent* fC, NodeId id,
                             NodeId unpackedDimension);

  void checkForLoops(bool on);
  bool loopDetected(PathId fileId, uint32_t lineNumber,
                    CompileDesign* compileDesign, ValuedComponentI* instance);

  uhdm::Any* getValue(std::string_view name, DesignComponent* component,
                      CompileDesign* compileDesign, Reduce reduce,
                      ValuedComponentI* instance, PathId fileId,
                      uint32_t lineNumber, uhdm::Any* pexpr,
                      bool muteErrors = false);

  // Parse numeric UHDM constant into int64_t. Returns if successful.
  bool parseConstant(const uhdm::Constant& constant, int64_t* value);

  int64_t getValue(bool& validValue, DesignComponent* component,
                   const FileContent* fC, NodeId nodeId,
                   CompileDesign* compileDesign, Reduce reduce,
                   uhdm::Any* pexpr, ValuedComponentI* instance,
                   bool muteErrors = false);

  uhdm::Typespec* elabTypespec(DesignComponent* component, uhdm::Typespec* spec,
                               CompileDesign* compileDesign,
                               uhdm::Any* pexpr = nullptr,
                               ValuedComponentI* instance = nullptr);

  bool substituteAssignedValue(const uhdm::Any* op,
                               CompileDesign* compileDesign);

  uhdm::Any* getObject(std::string_view name, DesignComponent* component,
                       CompileDesign* compileDesign, ValuedComponentI* instance,
                       const uhdm::Any* pexpr);

  void reorderAssignmentPattern(DesignComponent* mod, const uhdm::Any* lhs,
                                uhdm::Any* rhs, CompileDesign* compileDesign,
                                ValuedComponentI* instance, uint32_t level);

  bool errorOnNegativeConstant(DesignComponent* component, uhdm::Expr* exp,
                               CompileDesign* compileDesign,
                               ValuedComponentI* instance);
  bool errorOnNegativeConstant(DesignComponent* component, Value* value,
                               CompileDesign* compileDesign,
                               ValuedComponentI* instance);
  bool errorOnNegativeConstant(DesignComponent* component,
                               std::string_view value,
                               CompileDesign* compileDesign,
                               ValuedComponentI* instance, PathId fileId,
                               uint32_t lineNo, uint16_t columnNo);

  uhdm::Any* decodeHierPath(uhdm::HierPath* path, bool& invalidValue,
                            DesignComponent* component,
                            CompileDesign* compileDesign, Reduce reduce,
                            ValuedComponentI* instance, PathId fileName,
                            uint32_t lineNumber, uhdm::Any* pexpr,
                            bool muteErrors, bool returnTypespec);

  bool valueRange(Value* val, const uhdm::Typespec* lhstps,
                  const uhdm::Typespec* rhstps, DesignComponent* component,
                  CompileDesign* compileDesign, ValuedComponentI* instance);

  void setRange(uhdm::Constant* c, Value* val, CompileDesign* compileDesign);

  uhdm::Constant* adjustSize(const uhdm::Typespec* ts,
                             DesignComponent* component,
                             CompileDesign* compileDesign,
                             ValuedComponentI* instance, uhdm::Constant* c,
                             bool uniquify = false, bool sizeMode = false);

  /** task/func/scope */
  uhdm::Any* searchObjectName(std::string_view name, DesignComponent* component,
                              CompileDesign* compileDesign, uhdm::Any* stmt);

  bool isOverloaded(const uhdm::Any* expr, CompileDesign* compileDesign,
                    ValuedComponentI* instance);

  std::string decompileHelper(const uhdm::Any* sel);

  Elaborate getElaborate() const { return m_elaborate; }
  void setElaborate(Elaborate elaborate) { m_elaborate = elaborate; }

  Reduce getReduce() const { return m_reduce; }
  void setReduce(Reduce reduce) { m_reduce = reduce; }

 private:
  // Caches
  uhdm::IntTypespec* buildIntTypespec(CompileDesign* compileDesign,
                                      PathId fileId, std::string_view name,
                                      std::string_view value, uint32_t line,
                                      uint16_t column, uint32_t eline,
                                      uint16_t ecolumn);
  uhdm::TypespecMember* buildTypespecMember(CompileDesign* compileDesign,
                                            const FileContent* fC, NodeId id);

 private:
  Session* const m_session = nullptr;
  ExprBuilder m_exprBuilder;
  uhdm::Module* m_exprEvalPlaceHolder = nullptr;
  bool m_checkForLoops = false;
  int32_t m_stackLevel = 0;
  bool m_unwind = false;
  Elaborate m_elaborate = Elaborate::Yes;
  Reduce m_reduce = Reduce::Yes;
};

}  // namespace SURELOG

#endif /* SURELOG_COMPILEHELPER_H */
