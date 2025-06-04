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
 * File:   CompilePackage.h
 * Author: alain
 *
 * Created on March 22, 2018, 9:57 PM
 */

#ifndef SURELOG_COMPILEPACKAGE_H
#define SURELOG_COMPILEPACKAGE_H
#pragma once

#include <Surelog/DesignCompile/CompileHelper.h>

#include <cstdint>

// UHDM
#include <uhdm/containers.h>

namespace SURELOG {
class CompileDesign;
class Design;
class Package;
class Session;

struct FunctorCompilePackage final {
  FunctorCompilePackage(Session* session, CompileDesign* compileDesign,
                        Package* package, Design* design)
      : m_session(session),
        m_compileDesign(compileDesign),
        m_package(package),
        m_design(design) {}
  int32_t operator()() const;

 private:
  Session* const m_session = nullptr;
  CompileDesign* const m_compileDesign = nullptr;
  Package* const m_package = nullptr;
  Design* const m_design = nullptr;
};

class CompilePackage final {
 public:
  CompilePackage(Session* session, CompileDesign* compileDesign,
                 Package* package, Design* design)
      : m_session(session),
        m_compileDesign(compileDesign),
        m_package(package),
        m_design(design),
        m_helper(session) {}

  bool compile(Elaborate elaborate, Reduce reduce);

 private:
  enum CollectType { FUNCTION, DEFINITION, OTHER };
  bool collectObjects_(CollectType collectType, Reduce reduce);

  Session* const m_session = nullptr;
  CompileDesign* const m_compileDesign;
  Package* const m_package;
  Design* const m_design;
  CompileHelper m_helper;
  uhdm::AttributeCollection* m_attributes = nullptr;
};

}  // namespace SURELOG

#endif /* SURELOG_COMPILEPACKAGE_H */
