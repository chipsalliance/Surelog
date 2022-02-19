/*
 Copyright 2021 Alain Dargelas

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
 * File:   ParserHarness.h
 * Author: alain
 *
 * Created on June 5, 2021, 10:00 AM
 */

#ifndef SURELOG_PARSERHARNESS_H
#define SURELOG_PARSERHARNESS_H
#pragma once

#include <memory>
#include <string>

#include "Surelog/Design/FileContent.h"
#include "Surelog/SourceCompile/Compiler.h"

namespace SURELOG {

class ParserHarness {
 public:
  // Parse content and return FileContent or nullptr if it couldn't
  // be parsed.
  // Unit test
  std::unique_ptr<FileContent> parse(const std::string& content);

  // Builtin
  FileContent* parse(const std::string& content, Compiler* compiler,
                     const std::string fileName);
  ~ParserHarness();

 private:
  struct Holder;
  Holder* m_h = nullptr;
};

};  // namespace SURELOG

#endif /* SURELOG_PARSERHARNESS_H */
