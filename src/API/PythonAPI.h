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
#include <string>
#include <vector>

#include "ErrorReporting/ErrorContainer.h"

#ifndef PYTHONAPI_H
#define PYTHONAPI_H
#ifdef SURELOG_WITH_PYTHON
#include "Python.h"
#else
#define PyThreadState void
#endif

namespace SURELOG {

class SV3_1aPythonListener;
class FileContent;
class Design;
struct parser_rule_context;

class PythonAPI {
 public:
  PythonAPI();
  virtual ~PythonAPI();
  /* Main interpreter (in main thread) */
  static void init(int argc, const char** argv);
  static void shutdown();
  static PyThreadState* getMainInterp() { return m_mainThreadState; }
  /* Per thread interpreters */
  static PyThreadState* initNewInterp();
  static void shutdown(PyThreadState* interp);

  static void loadScripts();
  static bool loadScript(std::string name, bool check = false);
  static std::string evalScript(std::string module, std::string function,
                                std::vector<std::string> args,
                                PyThreadState* interp);
  static void evalScript(std::string function, SV3_1aPythonListener* listener,
                         parser_rule_context* ctx);
  static std::string getInvalidScriptString() { return m_invalidScriptResult; }
  static bool isListenerLoaded() { return m_listenerLoaded; }
  static std::string getListenerScript() { return m_listenerScript; }
  static void setListenerScript(std::string script) {
    m_listenerScript = script;
  }
  static bool evalScriptPerFile(std::string script, ErrorContainer* errors,
                                FileContent* fC, PyThreadState* interp);
  static bool evalScript(std::string script, Design* design);
  static void setStrictMode(bool mode) { m_strictMode = mode; }

 private:
  PythonAPI(const PythonAPI& orig) = delete;

  static void initInterp_();
  static void loadScriptsInInterp_();
  static bool loadScript_(std::string name, bool check = false);
  static std::string m_invalidScriptResult;
  static PyThreadState* m_mainThreadState;
  static std::string m_programPath;
  static bool m_listenerLoaded;
  static std::string m_listenerScript;
  static bool m_strictMode;
  static std::string m_builtinPath;
};

};  // namespace SURELOG

#endif /* PYTHONAPI_H */
