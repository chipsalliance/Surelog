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
 * File:   FunctionMethod.cpp
 * Author: alain
 *
 * Created on February 21, 2019, 8:20 PM
 */

#include "FunctionMethod.h"

using namespace SURELOG;

FunctionMethod::~FunctionMethod() {}

bool FunctionMethod::compile(CompileHelper& compile_helper) {
  bool result = Function::compile(compile_helper);
  return result;
}
