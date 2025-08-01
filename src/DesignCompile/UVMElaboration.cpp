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
 * File:   UVMElaboration.cpp
 * Author: alain
 *
 * Created on July 12, 2017, 8:56 PM
 */

#include "Surelog/DesignCompile/UVMElaboration.h"

#include "Surelog/DesignCompile/TestbenchElaboration.h"

namespace SURELOG {

UVMElaboration::UVMElaboration(CompileDesign* compileDesign)
    : TestbenchElaboration(compileDesign) {}

bool UVMElaboration::elaborate() {
  bindClasses_();
  return true;
}

}  // namespace SURELOG
