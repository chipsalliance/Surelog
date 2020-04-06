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
 * File:   CompileStmt.cpp
 * Author: alain
 *
 * Created on May 14, 2019, 8:03 PM
 */
#include <iostream>
#include "Expression/Value.h"
#include "Expression/ExprBuilder.h"
#include "Design/Enum.h"
#include "Design/Function.h"
#include "Testbench/Property.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/ParseFile.h"
#include "SourceCompile/Compiler.h"
#include "Design/Design.h"
#include "DesignCompile/CompileHelper.h"
#include "CompileDesign.h"
#include "uhdm.h"
#include "expr.h"
#include "UhdmWriter.h"

using namespace SURELOG;

UHDM::any* CompileHelper::compileStmt(FileContent* fC, NodeId the_stmt, 
        CompileDesign* compileDesign, UHDM::any* pstmt) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  VObjectType type = fC->Type(the_stmt);
  UHDM::any* stmt = nullptr;
  switch (type) {
  case VObjectType::slStatement_or_null:
  case VObjectType::slStatement:
  case VObjectType::slStatement_item: {
	return compileStmt(fC, fC->Child(the_stmt), compileDesign);
  }
  case VObjectType::slProcedural_timing_control_statement:{
    UHDM::atomic_stmt* dc = compileProceduralTimingControlStmt(fC, the_stmt, compileDesign);
    stmt = dc;        
    break;
  }
  case VObjectType::slNonblocking_assignment: {
    NodeId Operator_assignment  = the_stmt;
    UHDM::assignment* assign = compileBlockingAssignment(fC, 
                Operator_assignment, false, compileDesign);
    stmt = assign; 
    break; 
  }
  case VObjectType::slBlocking_assignment: {
    NodeId Operator_assignment = fC->Child(the_stmt);
    UHDM::assignment* assign = compileBlockingAssignment(fC, 
                Operator_assignment, true, compileDesign);
    stmt = assign;    
    break;
  }
  case VObjectType::slSubroutine_call_statement: {
	NodeId Subroutine_call = fC->Child(the_stmt);
    UHDM::tf_call* call = compileTfCall(fC, Subroutine_call ,compileDesign);
	stmt = call;
	break;
  }
  case VObjectType::slConditional_statement: {
	NodeId Conditional_statement = the_stmt;  
	UHDM::atomic_stmt* cstmt = compileConditionalStmt(fC, 
                                   Conditional_statement, compileDesign);
	stmt = cstmt;
	break;
  }
  case VObjectType::slSeq_block: {
	NodeId item = fC->Child(the_stmt);
	UHDM::begin* begin = s.MakeBegin();
	VectorOfany* stmts = s.MakeAnyVec();
	while (item) {
	  UHDM::any* cstmt = compileStmt(fC, item, compileDesign);
	  if (cstmt)
	    stmts->push_back(cstmt);
	  item = fC->Sibling(item);	
	}
	begin->Stmts(stmts);
	stmt = begin;
	break;
  }
  default:
    break;
  }
  return stmt;
}
