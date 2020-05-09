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
#include "SourceCompile/VObjectTypes.h"
#include "Design/DataType.h"
#include "Design/TfPortItem.h"
#include "Expression/ExprBuilder.h"
#include "ErrorReporting/ErrorContainer.h"
#include "Common/PortNetHolder.h"
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

  bool compilePortDeclaration(PortNetHolder* scope, FileContent* fC,
                              NodeId id, VObjectType& port_direction);
  
  bool compileAnsiPortDeclaration(PortNetHolder* component,
        FileContent* fC, NodeId id, VObjectType& port_direction);
  
  bool compileNetDeclaration(PortNetHolder* component, 
        FileContent* fC, NodeId id, bool interface);
  
  bool compileDataDeclaration(DesignComponent* component, 
        PortNetHolder* portholder,
        FileContent* fC, NodeId id, 
        bool interface,
        CompileDesign* compileDesign);

// ------------------------------------------------------------------------------------------
// UHDM modeling 

  bool compileContinuousAssignment(PortNetHolder* component,
        FileContent* fC, NodeId id, CompileDesign* compileDesign); 
  
  bool compileAlwaysBlock(PortNetHolder* component, FileContent* fC, 
        NodeId id, CompileDesign* compileDesign);

  UHDM::tf_call* compileTfCall(PortNetHolder* component, FileContent* fC,
        NodeId Tf_call_stmt,
        CompileDesign* compileDesign);

  UHDM::VectorOfany* compileTfCallArguments(PortNetHolder* component, FileContent* fC,
        NodeId Arg_list_node,
        CompileDesign* compileDesign);

  UHDM::assignment* compileBlockingAssignment(PortNetHolder* component, FileContent* fC, NodeId nodeId, 
        bool blocking, CompileDesign* compileDesign);

  UHDM::atomic_stmt* compileProceduralTimingControlStmt(PortNetHolder* component, FileContent* fC, NodeId nodeId, 
        CompileDesign* compileDesign);

  UHDM::atomic_stmt* compileEventControlStmt(PortNetHolder* component, FileContent* fC, 
        NodeId nodeId, 
        CompileDesign* compileDesign) ;
  
  UHDM::atomic_stmt* compileConditionalStmt(PortNetHolder* component, FileContent* fC, NodeId nodeId, 
        CompileDesign* compileDesign);

  bool compileParameterDeclaration(PortNetHolder* component, FileContent* fC, NodeId nodeId, 
        CompileDesign* compileDesign, bool localParam = false);
  
  bool compileTask(PortNetHolder* component, FileContent* fC, NodeId nodeId, 
        CompileDesign* compileDesign);

  bool compileFunction(PortNetHolder* component, FileContent* fC, NodeId nodeId, 
        CompileDesign* compileDesign);   

  std::vector<UHDM::io_decl*>* compileTfPortList(UHDM::task_func* parent, FileContent* fC, NodeId id,
                         CompileDesign* compileDesign);         

  UHDM::atomic_stmt* compileCaseStmt(PortNetHolder* component, FileContent* fC, NodeId nodeId, 
        CompileDesign* compileDesign);      

  UHDM::any* compileStmt(PortNetHolder* component, FileContent* fC, NodeId nodeId, 
        CompileDesign* compileDesign, UHDM::any* pstmt = NULL);

  UHDM::any* compileVariable(FileContent* fC, NodeId nodeId, 
        CompileDesign* compileDesign, UHDM::any* pstmt = NULL); 

  UHDM::typespec* compileTypespec(DesignComponent* component, FileContent* fC, NodeId nodeId, 
        CompileDesign* compileDesign, UHDM::any* pstmt = NULL);                      

  UHDM::any* compileImmediateAssertion(PortNetHolder* component, FileContent* fC, NodeId nodeId, 
        CompileDesign* compileDesign, UHDM::any* pstmt = NULL);

  bool compileInitialBlock(PortNetHolder* component, FileContent* fC, 
        NodeId id, CompileDesign* compileDesign);
  
  UHDM::constant* constantFromValue(Value* val, CompileDesign* compileDesign);

  UHDM::any* compileExpression(PortNetHolder* component, FileContent* fC, NodeId nodeId, 
			       	CompileDesign* compileDesign,
                              UHDM::expr* pexpr = NULL, 
                              ValuedComponentI* instance = NULL);

  UHDM::any* compilePartSelectRange(PortNetHolder* component, FileContent* fC, NodeId Constant_range,
                                       const std::string& name,
                                       CompileDesign* compileDesign,
                                       UHDM::expr* pexpr,
                                       ValuedComponentI* instance);

  UHDM::any* compileAssignmentPattern(PortNetHolder* component, FileContent* fC, NodeId Assignment_pattern, 
                                       CompileDesign* compileDesign,
                                       UHDM::expr* pexpr,
                                       ValuedComponentI* instance); 

  virtual ~CompileHelper();

 private:
  ErrorContainer* m_errors;
  SymbolTable* m_symbols;
  ExprBuilder m_exprBuilder;
};

};  // namespace SURELOG

#endif /* COMPILEHELPER_H */
