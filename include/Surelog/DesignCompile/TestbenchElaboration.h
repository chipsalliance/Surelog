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
 * File:   TestbenchElaboration.h
 * Author: alain
 *
 * Created on February 6, 2019, 9:01 PM
 */

#ifndef SURELOG_TESTBENCHELABORATION_H
#define SURELOG_TESTBENCHELABORATION_H
#pragma once

#include <Surelog/Design/Design.h>
#include <Surelog/DesignCompile/ElaborationStep.h>

namespace SURELOG {

class ClassDefinition;
class ForeachLoopStmt;
class ForLoopStmt;
class Procedure;
class Statement;
class Variable;

class TestbenchElaboration : public ElaborationStep {
 public:
  explicit TestbenchElaboration(CompileDesign* compileDesign)
      : ElaborationStep(compileDesign) {}

  TestbenchElaboration(const TestbenchElaboration& orig);

  ~TestbenchElaboration() override = default;

 protected:
  bool checkForMultipleDefinition_();
  bool bindClasses_();
  bool bindBaseClasses_();
  bool bindProperties_();
  virtual bool bindDataTypes_();
  bool bindFunctions_();
  bool bindTasks_();
  bool bindFunctionReturnTypesAndParamaters_();
  bool bindFunctionBodies_();
  bool bindSubRoutineCall_(ClassDefinition* classDefinition, Statement* stmt,
                           Design* design, SymbolTable* symbols,
                           ErrorContainer* errors);
  bool bindForeachLoop_(ClassDefinition* classDefinition, Statement* stmt,
                        ForeachLoopStmt* st);
  bool bindForLoop_(ClassDefinition* classDefinition, Statement* stmt,
                    ForLoopStmt* st);
};

}  // namespace SURELOG

#endif /* SURELOG_TESTBENCHELABORATION_H */
