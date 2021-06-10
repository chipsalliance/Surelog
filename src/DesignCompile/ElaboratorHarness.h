/*
 Copyright 2017-2021 Alain Dargelas

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
 * File:   ElaboratorHarness.h
 * Author: alain
 *
 * Created on June 8, 2021, 10:00 PM
 */

#ifndef ELABORATORHARNESS_H
#define ELABORATORHARNESS_H

#include "Design/Netlist.h"
#include "DesignCompile/ElaborationStep.h"
#include "Expression/ExprBuilder.h"
#include "TestbenchElaboration.h"

namespace SURELOG {

class ElaboratorHarness {
 public:
  std::tuple<Design*, FileContent*, CompileDesign*> elaborate(const std::string& text);

 public:
 private:
};

};  // namespace SURELOG

#endif /* ELABORATORHARNESS_H */
