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

#ifndef SURELOG_CHECKCOMPILE_H
#define SURELOG_CHECKCOMPILE_H
#pragma once

namespace SURELOG {
class Compiler;
class Session;

class CheckCompile {
 public:
  explicit CheckCompile(Session* session, Compiler* compiler);
  ~CheckCompile() = default;

  bool check();

 private:
  bool mergeSymbolTables_();

  bool checkTimescale_();

  bool checkSyntaxErrors_();

 private:
  Session* const m_session = nullptr;
  Compiler* const m_compiler = nullptr;
};

};  // namespace SURELOG

#endif /* SURELOG_CHECKCOMPILE_H */
