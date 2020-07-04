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

#ifndef COMPILEHELPER_H
#define COMPILEHELPER_H
#include <string>
#include "SourceCompile/SymbolTable.h"
#include "Design/FileContent.h"
#include "Design/DesignComponent.h"
#include "SourceCompile/VObjectTypes.h"
#include "Design/DataType.h"
#include "Design/TfPortItem.h"
#include "Expression/ExprBuilder.h"
#include "ErrorReporting/ErrorContainer.h"
#include "headers/uhdm_forward_decl.h"

namespace SURELOG {
class Scope;
class Statement;
class Design;
class CompileDesign;
typedef std::vector<TfPortItem*> TfPortList;

class CompileHelper {
 public:
  CompileHelper() {}

  void seterrorReporting(ErrorContainer* errors, SymbolTable* symbols) {
    m_errors = errors;
    m_symbols = symbols;
    m_exprBuilder.seterrorReporting(errors, symbols);
  }

// ------------------------------------------------------------------------------------------
// Surelog internal modeling 

  bool importPackage(DesignComponent* scope, Design* design, FileContent* fC,
                     NodeId id);

  bool compileTfPortList(Procedure* parent, FileContent* fC, NodeId id,
                         TfPortList& targetList);

  DataType* compileTypeDef(DesignComponent* scope, FileContent* fC, NodeId id,
        CompileDesign* compileDesign);

  bool compileScopeBody(Scope* parent, Statement* parentStmt, FileContent* fC,
                        NodeId id);

  bool compileScopeVariable(Scope* parent, FileContent* fC, NodeId id);

  bool compileSubroutine_call(Scope* parent, Statement* parentStmt,
                              FileContent* fC, NodeId id);

  bool compileSeqBlock_stmt(Scope* parent, Statement* parentStmt,
                            FileContent* fC, NodeId id);

  bool compileLoop_stmt(Scope* parent, Statement* parentStmt, FileContent* fC,
                        NodeId id);

  bool compileForLoop_stmt(Scope* parent, Statement* parentStmt,
                           FileContent* fC, NodeId id);

  bool compileForeachLoop_stmt(Scope* parent, Statement* parentStmt,
                               FileContent* fC, NodeId id);

  Function* compileFunctionPrototype(DesignComponent* scope, FileContent* fC,
                                     NodeId id);

  bool compilePortDeclaration(DesignComponent* scope, FileContent* fC,
                              NodeId id, VObjectType& port_direction);
  
  bool compileAnsiPortDeclaration(DesignComponent* component,
        FileContent* fC, NodeId id, VObjectType& port_direction);
  
  bool compileNetDeclaration(DesignComponent* component, 
        FileContent* fC, NodeId id, bool interface);
  
  bool compileDataDeclaration(DesignComponent* component,
        FileContent* fC, NodeId id, 
        bool interface,
        CompileDesign* compileDesign);

// ------------------------------------------------------------------------------------------
// UHDM modeling 

  bool compileContinuousAssignment(DesignComponent* component,
        FileContent* fC, NodeId id, CompileDesign* compileDesign); 
  
  bool compileAlwaysBlock(DesignComponent* component, FileContent* fC, 
        NodeId id, CompileDesign* compileDesign);

  UHDM::tf_call* compileTfCall(DesignComponent* component, FileContent* fC,
        NodeId Tf_call_stmt,
        CompileDesign* compileDesign);

  UHDM::VectorOfany* compileTfCallArguments(DesignComponent* component, FileContent* fC,
        NodeId Arg_list_node,
        CompileDesign* compileDesign, UHDM::any* call);

  UHDM::assignment* compileBlockingAssignment(DesignComponent* component, FileContent* fC, NodeId nodeId, 
        bool blocking, CompileDesign* compileDesign);

  UHDM::atomic_stmt* compileProceduralTimingControlStmt(DesignComponent* component, FileContent* fC, NodeId nodeId, 
        CompileDesign* compileDesign);

  UHDM::atomic_stmt* compileEventControlStmt(DesignComponent* component, FileContent* fC, 
        NodeId nodeId, 
        CompileDesign* compileDesign) ;
  
  UHDM::atomic_stmt* compileConditionalStmt(DesignComponent* component, FileContent* fC, NodeId nodeId, 
        CompileDesign* compileDesign);

  bool compileParameterDeclaration(DesignComponent* component, FileContent* fC, NodeId nodeId, 
        CompileDesign* compileDesign, bool localParam = false, ValuedComponentI* m_instance = nullptr);
  
  bool compileTask(DesignComponent* component, FileContent* fC, NodeId nodeId, 
        CompileDesign* compileDesign);

  bool compileFunction(DesignComponent* component, FileContent* fC, NodeId nodeId, 
        CompileDesign* compileDesign);   

  std::vector<UHDM::io_decl*>* compileTfPortList(DesignComponent* scope, UHDM::task_func* parent, FileContent* fC, NodeId id,
                         CompileDesign* compileDesign);

  std::vector<UHDM::io_decl*>* compileTfPortDecl(DesignComponent* scope, UHDM::task_func* parent, FileContent* fC, NodeId id,
                         CompileDesign* compileDesign);                                         

  UHDM::atomic_stmt* compileCaseStmt(DesignComponent* component, FileContent* fC, NodeId nodeId, 
        CompileDesign* compileDesign);      

  UHDM::VectorOfany* compileStmt(DesignComponent* component, FileContent* fC, NodeId nodeId, 
        CompileDesign* compileDesign, UHDM::any* pstmt = NULL);

  UHDM::any* compileVariable(DesignComponent* component, FileContent* fC, NodeId nodeId, 
        CompileDesign* compileDesign, UHDM::any* pstmt, ValuedComponentI* instance, bool reduce); 

  UHDM::typespec* compileTypespec(DesignComponent* component, FileContent* fC, NodeId nodeId, 
        CompileDesign* compileDesign, UHDM::any* pstmt, ValuedComponentI* instance, bool reduce, const std::string& suffixname = "");                      

  UHDM::any* compileImmediateAssertion(DesignComponent* component, FileContent* fC, NodeId nodeId, 
        CompileDesign* compileDesign, UHDM::any* pstmt, ValuedComponentI* instance);

  bool compileInitialBlock(DesignComponent* component, FileContent* fC, 
        NodeId id, CompileDesign* compileDesign);
  
  UHDM::constant* constantFromValue(Value* val, CompileDesign* compileDesign);

  UHDM::any* compileExpression(DesignComponent* component, FileContent* fC, NodeId nodeId, 
			       	CompileDesign* compileDesign,
                              UHDM::any* pexpr = NULL, 
                              ValuedComponentI* instance = NULL, bool reduce = false);

  UHDM::any* compilePartSelectRange(DesignComponent* component, FileContent* fC, NodeId Constant_range,
                                       const std::string& name,
                                       CompileDesign* compileDesign,
                                       UHDM::any* pexpr,
                                       ValuedComponentI* instance);

  std::vector<UHDM::range*>* compileRanges(DesignComponent* component, FileContent* fC, NodeId Packed_dimension, 
                                       CompileDesign* compileDesign,
                                       UHDM::any* pexpr,
                                       ValuedComponentI* instance, bool reduce, int& size);

  UHDM::any* compileAssignmentPattern(DesignComponent* component, FileContent* fC, NodeId Assignment_pattern, 
                                       CompileDesign* compileDesign,
                                       UHDM::any* pexpr,
                                       ValuedComponentI* instance); 

  UHDM::array_var* compileArrayVar(DesignComponent* component, FileContent* fC, NodeId varId, 
                                   CompileDesign* compileDesign,
                                   UHDM::any* pexpr,
                                   ValuedComponentI* instance);      

  UHDM::any* compileProceduralContinuousAssign(DesignComponent* component, FileContent* fC, NodeId nodeId, 
        CompileDesign* compileDesign); 

  UHDM::VectorOfany* compileDataDeclaration(DesignComponent* component, FileContent* fC, NodeId nodeId, 
        CompileDesign* compileDesign);                                  

  UHDM::any* compileForLoop(DesignComponent* component, FileContent* fC, NodeId nodeId, 
        CompileDesign* compileDesign);

  UHDM::any* compileSelectExpression(DesignComponent* component,
                                            FileContent* fC, NodeId Bit_select,
                                            const std::string& name,
                                            CompileDesign* compileDesign,
                                            UHDM::any* pexpr,
                                            ValuedComponentI* instance);

  UHDM::any* compileBits(DesignComponent* component, FileContent* fC,
                         NodeId Expression,
                         CompileDesign* compileDesign, UHDM::any* pexpr,
                         ValuedComponentI* instance, bool reduce);

  UHDM::any* compileClog2(DesignComponent* component, FileContent* fC,
                         NodeId Expression,
                         CompileDesign* compileDesign, UHDM::any* pexpr,
                         ValuedComponentI* instance, bool reduce);

  const UHDM::typespec* getTypespec(DesignComponent* component, FileContent* fC,
                              NodeId id, CompileDesign* compileDesign, ValuedComponentI* instance, bool reduce);                      

  UHDM::any* compileComplexFuncCall(DesignComponent* component,
                                       FileContent* fC, NodeId nodeId,
                                       CompileDesign* compileDesign,
                                       UHDM::any* pexpr,
                                       ValuedComponentI* instance,
                                       bool reduce);

  virtual ~CompileHelper();

 private:
  ErrorContainer* m_errors;
  SymbolTable* m_symbols;
  ExprBuilder m_exprBuilder;
};

};  // namespace SURELOG

#endif /* COMPILEHELPER_H */
