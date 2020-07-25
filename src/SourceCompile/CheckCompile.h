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
 * File:   CheckCompile.h
 * Author: alain
 *
 * Created on June 10, 2017, 10:15 PM
 */

#ifndef CHECKCOMPILE_H
#define CHECKCOMPILE_H

namespace SURELOG {

class Compiler;

class CheckCompile {
 public:
  CheckCompile(Compiler* compiler) : m_compiler(compiler) {}
  bool check();
  virtual ~CheckCompile();

 private:
  bool mergeSymbolTables_();

  bool checkTimescale_();

  bool checkSyntaxErrors_();
  
  Compiler* m_compiler;
};

};  // namespace SURELOG

#endif /* CHECKCOMPILE_H */
