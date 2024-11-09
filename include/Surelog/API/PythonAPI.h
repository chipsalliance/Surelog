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
 * File:   PythonAPI.h
 * Author: alain
 *
 * Created on May 13, 2017, 4:42 PM
 */

#ifndef SURELOG_PYTHONAPI_H
#define SURELOG_PYTHONAPI_H
#pragma once

#include <filesystem>
#include <string>
#include <vector>

struct _ts;
using PyThreadState = struct _ts;

namespace SURELOG {

class Design;
class ErrorContainer;
class FileContent;
class SV3_1aPythonListener;
struct parser_rule_context;

class PythonAPI {
 public:
  PythonAPI() = default;
  PythonAPI(const PythonAPI& orig) = delete;

  virtual ~PythonAPI() = default;

  /* Main interpreter (in main thread) */
  static void init(int32_t argc, const char** argv);
  static void shutdown();
  static PyThreadState* getMainInterp() { return m_mainThreadState; }
  /* Per thread interpreters */
  static PyThreadState* initNewInterp();
  static void shutdown(PyThreadState* interp);

  static void loadScripts();
  static bool loadScript(const std::filesystem::path& name, bool check = false);
  static std::string evalScript(const std::string& module,
                                const std::string& function,
                                const std::vector<std::string>& args,
                                PyThreadState* interp);
  static void evalScript(std::string function, SV3_1aPythonListener* listener,
                         parser_rule_context* ctx);
  static std::string getInvalidScriptString() { return m_invalidScriptResult; }
  static bool isListenerLoaded() { return m_listenerLoaded; }
  static std::string getListenerScript() { return m_listenerScript.string(); }
  static void setListenerScript(const std::filesystem::path& script) {
    m_listenerScript = script;
  }
  static bool evalScriptPerFile(const std::filesystem::path& script,
                                ErrorContainer* errors, FileContent* fC,
                                PyThreadState* interp);
  static bool evalScript(const std::filesystem::path& script, Design* design);
  static void setStrictMode(bool mode) { m_strictMode = mode; }

 private:
  static void initInterp_();
  static void loadScriptsInInterp_();
  static bool loadScript_(const std::filesystem::path& name,
                          bool check = false);
  static std::string m_invalidScriptResult;
  static PyThreadState* m_mainThreadState;
  static std::filesystem::path m_programPath;
  static bool m_listenerLoaded;
  static std::filesystem::path m_listenerScript;
  static bool m_strictMode;
  static std::filesystem::path m_builtinPath;
};

};  // namespace SURELOG

#endif /* SURELOG_PYTHONAPI_H */
