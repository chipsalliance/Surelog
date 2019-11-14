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
 * File:   PythonAPI.cpp
 * Author: alain
 *
 * Created on May 13, 2017, 4:42 PM
 */

#include "../SourceCompile/SymbolTable.h"
#include "../Utils/StringUtils.h"
#include "../Utils/FileUtils.h"
#include "../CommandLine/CommandLineParser.hpp"
#include "../ErrorReporting/ErrorContainer.h"
#include "../SourceCompile/CompilationUnit.h"
#include "../SourceCompile/PreprocessFile.h"
#include "../SourceCompile/CompileSourceFile.h"
#include "../SourceCompile/Compiler.h"
#include "../SourceCompile/ParseFile.h"
#include "antlr4-runtime.h"
using namespace std;
using namespace antlr4;

#include "../parser/SV3_1aParserBaseListener.h"

#include "SV3_1aPythonListener.h"

using namespace SURELOG;

#include <sstream>
#include <string>
#include <fstream>
#include <iostream>
#include <cstdio>
#include "Python.h"
#include "PythonAPI.h"
#include "SLAPI.h"
#include "slapi_wrap.cxx"
#include "slapi.h"
#include "vobjecttypes_py.h"
#include <cstdlib>
#include "../SourceCompile/PythonListen.h"

std::string PythonAPI::m_invalidScriptResult = "INVALID_PYTHON_SCRIPT_RESULT";

PyThreadState* PythonAPI::m_mainThreadState = NULL;

std::string PythonAPI::m_programPath = "";

bool PythonAPI::m_listenerLoaded = false;

std::string PythonAPI::m_listenerScript;

bool PythonAPI::m_strictMode = false;

PythonAPI::PythonAPI() {}

PythonAPI::PythonAPI(const PythonAPI& orig) {}

PythonAPI::~PythonAPI() {}

static struct PyModuleDef SLAPI_module = {PyModuleDef_HEAD_INIT,
                                          "slapi",
                                          NULL,
                                          -1,
                                          SwigMethods,
                                          NULL,
                                          NULL,
                                          NULL,
                                          NULL};

static PyObject* PyInit_slapi(void) { return PyModule_Create(&SLAPI_module); }

void PythonAPI::shutdown() {
  PyEval_RestoreThread(m_mainThreadState);
  Py_Finalize();
}

bool PythonAPI::loadScript(std::string name, bool check) {
  PyEval_AcquireThread(m_mainThreadState);
  bool status = loadScript_(name, check);
  PyEval_ReleaseThread(m_mainThreadState);
  return status;
}

bool PythonAPI::loadScript_(std::string name, bool check) {
  if (FileUtils::fileExists(name)) {
    FILE* fp = fopen(name.c_str(), "r");
    PyRun_SimpleFile(fp, name.c_str());
    PyErr_Print();
    fclose(fp);
    return true;
  } else {
    if (check)
      std::cout << "PYTHON API ERROR: Script \"" << name
                << "\" does not exist.\n";
  }
  return false;
}

PyThreadState* PythonAPI::initNewInterp() {
  PyEval_AcquireThread(m_mainThreadState);
  PyThreadState* interpState = Py_NewInterpreter();

  loadScriptsInInterp_();
  // PyEval_ReleaseThread(m_mainThreadState);

  PyEval_ReleaseThread(interpState);
  return interpState;
}

void PythonAPI::shutdown(PyThreadState* interp) {
  if (interp != m_mainThreadState) {
    PyEval_AcquireThread(interp);
    Py_EndInterpreter(interp);
    PyEval_ReleaseLock();
  }
}

void PythonAPI::loadScriptsInInterp_() {
  // Loads the python SWIG generated defs
  std::string script;
  for (auto s : slapi_scripts) {
    script += s;
  }
  for (auto s : slapi_types) {
    script += s;
  }
  PyRun_SimpleString(script.c_str());

  PyRun_SimpleString("import sys");
  PyRun_SimpleString("sys.path.append(\".\")");
  PyRun_SimpleString(
      std::string("sys.path.append(\"" + m_programPath + "\")").c_str());

  std::string waivers = m_programPath + "/../python/slwaivers.py";
  bool waiverLoaded = loadScript_(waivers);

  const char* home = getenv("HOME");
  if (home) {
    waivers = std::string(home) + "/slwaivers.py";
    waiverLoaded = loadScript_(waivers) || waiverLoaded;
  }

  waivers = "./slwaivers.py";
  waiverLoaded = loadScript_(waivers) || waiverLoaded;

  std::string format = m_programPath + "/../python/slformatmsg.py";
  bool messageFormatLoaded = loadScript_(format);

  if (home) {
    format = std::string(home) + "/slformatmsg.py";
    messageFormatLoaded = loadScript_(format) || messageFormatLoaded;
  }

  format = "./slformatmsg.py";
  messageFormatLoaded = loadScript_(format) || messageFormatLoaded;

  if (m_listenerScript != "") {
    if (FileUtils::fileExists(m_listenerScript)) {
      m_listenerLoaded = loadScript_(m_listenerScript);
    }
  }

  if (!m_listenerLoaded) {
    std::string listener =
        m_programPath + "/../python/slSV3_1aPythonListener.py";
    if (FileUtils::fileExists(listener)) m_listenerScript = listener;
    m_listenerLoaded = loadScript_(listener);

    if (home) {
      listener = std::string(home) + "/slSV3_1aPythonListener.py";
      if (FileUtils::fileExists(listener)) m_listenerScript = listener;
      m_listenerLoaded = loadScript_(listener) || m_listenerLoaded;
    }

    listener = "./slSV3_1aPythonListener.py";
    if (FileUtils::fileExists(listener)) m_listenerScript = listener;
    m_listenerLoaded = loadScript_(listener) || m_listenerLoaded;
  }
}

void PythonAPI::init(const char** argv) {
  m_programPath = argv[0];
  m_programPath = StringUtils::rtrim(m_programPath, '/');

  Py_SetProgramName((wchar_t*)argv[0]); /* optional but recommended */

  PyImport_AppendInittab("slapi", &PyInit_slapi);

  Py_Initialize();
  PyEval_InitThreads();
  m_mainThreadState = PyEval_SaveThread();
  PyEval_AcquireThread(m_mainThreadState);

  loadScriptsInInterp_();

  PyEval_ReleaseThread(m_mainThreadState);
}

void PythonAPI::evalScript(std::string function, SV3_1aPythonListener* listener,
                           ParserRuleContext* ctx) {
  PyEval_AcquireThread(listener->getPyThreadState());
  PyObject *pModuleName, *pModule, *pFunc;
  PyObject *pArgs, *pValue;
  pModuleName = PyString_FromString("__main__");
  pModule = PyImport_Import(pModuleName);
  Py_DECREF(pModuleName);
  pFunc = PyObject_GetAttrString(pModule, function.c_str());
  if (!pFunc || !PyCallable_Check(pFunc)) {
    if (m_strictMode)
      std::cout << "PYTHON API ERROR: Function \"" << function
                << "\" does not exist.\n";
    PyEval_ReleaseThread(listener->getPyThreadState());
    return;
  }
  pArgs = PyTuple_New(2);
  pValue = SWIG_NewPointerObj(SWIG_as_voidptr(listener),
                              SWIGTYPE_p_SURELOG__SV3_1aPythonListener, 0 | 0);
  PyTuple_SetItem(pArgs, 0, pValue);
  pValue = SWIG_NewPointerObj(SWIG_as_voidptr(ctx),
                              SWIGTYPE_p_ParserRuleContext, 0 | 0);
  PyTuple_SetItem(pArgs, 1, pValue);
  PyObject_CallObject(pFunc, pArgs);
  PyErr_Print();
  Py_DECREF(pArgs);
  Py_XDECREF(pFunc);
  Py_DECREF(pModule);
  PyEval_ReleaseThread(listener->getPyThreadState());
}

std::string PythonAPI::evalScript(std::string module, std::string function,
                                  std::vector<std::string> args,
                                  PyThreadState* interp) {
  PyEval_AcquireThread(interp);

  std::string result;
  PyObject *pModuleName, *pModule, *pFunc;
  PyObject *pArgs, *pValue;

  pModuleName = PyString_FromString(module.c_str());
  pModule = PyImport_Import(pModuleName);

  Py_DECREF(pModuleName);
  if (pModule != NULL) {
    pFunc = PyObject_GetAttrString(pModule, function.c_str());
    /* pFunc is a new reference */

    if (pFunc && PyCallable_Check(pFunc)) {
      pArgs = PyTuple_New(args.size());
      for (unsigned int i = 0; i < args.size(); ++i) {
        pValue = PyString_FromString(args[i].c_str());
        /* pValue reference stolen here: */
        PyTuple_SetItem(pArgs, i, pValue);
      }
      pValue = PyObject_CallObject(pFunc, pArgs);
      Py_DECREF(pArgs);
      if (pValue != NULL) {
        long int size;
        const char* compName = PyUnicode_AsUTF8AndSize(pValue, &size);
        if (compName == NULL) {
          std::cout << "PYTHON API ERROR: Incorrect function return type, "
                       "expecting a string: "
                    << function << std::endl;
          Py_DECREF(pValue);

          PyEval_ReleaseThread(interp);
          return m_invalidScriptResult;
        }
        result = compName;
        Py_DECREF(pValue);
      } else {
        Py_DECREF(pFunc);
        Py_DECREF(pModule);
        PyErr_Print();
        std::cout << "PYTHON API ERROR: Incorrect function evaluation: "
                  << function << std::endl;
        PyEval_ReleaseThread(interp);
        return m_invalidScriptResult;
      }
    } else {
      if (PyErr_Occurred()) PyErr_Print();
      std::cout << "PYTHON API ERROR: Cannot find function " << function
                << std::endl;

      PyEval_ReleaseThread(interp);
      return m_invalidScriptResult;
    }
    Py_XDECREF(pFunc);
    Py_DECREF(pModule);
  } else {
    PyErr_Print();
    std::cout << "PYTHON API ERROR: Cannot load module " << module << std::endl;
    return m_invalidScriptResult;
  }

  PyEval_ReleaseThread(interp);
  return result;
}

bool PythonAPI::evalScriptPerFile(std::string script, ErrorContainer* errors,
                                  FileContent* fC, PyThreadState* interp) {
  PyEval_AcquireThread(interp);
  loadScript_(script);
  std::string function = "slUserCallbackPerFile";
  PyObject *pModuleName, *pModule, *pFunc;
  PyObject *pArgs, *pValue;
  pModuleName = PyString_FromString("__main__");
  pModule = PyImport_Import(pModuleName);
  Py_DECREF(pModuleName);
  pFunc = PyObject_GetAttrString(pModule, function.c_str());
  if (!pFunc || !PyCallable_Check(pFunc)) {
    std::cout << "PYTHON API ERROR: Function \"" << function
              << "\" does not exist.\n";
    PyEval_ReleaseThread(interp);
    return false;
  }
  pArgs = PyTuple_New(2);
  pValue = SWIG_NewPointerObj(SWIG_as_voidptr(errors),
                              SWIGTYPE_p_SURELOG__ErrorContainer, 0 | 0);
  PyTuple_SetItem(pArgs, 0, pValue);
  pValue = SWIG_NewPointerObj(SWIG_as_voidptr(fC),
                              SWIGTYPE_p_SURELOG__FileContent, 0 | 0);
  PyTuple_SetItem(pArgs, 1, pValue);

  PyObject_CallObject(pFunc, pArgs);
  PyErr_Print();
  Py_DECREF(pArgs);
  Py_XDECREF(pFunc);
  Py_DECREF(pModule);

  PyEval_ReleaseThread(interp);
  return true;
}

bool PythonAPI::evalScript(std::string script, Design* design) {
  PyEval_AcquireThread(m_mainThreadState);
  loadScript_(script);
  std::string function = "slUserCallbackPerDesign";
  PyObject *pModuleName, *pModule, *pFunc;
  PyObject *pArgs, *pValue;
  pModuleName = PyString_FromString("__main__");
  pModule = PyImport_Import(pModuleName);
  Py_DECREF(pModuleName);
  pFunc = PyObject_GetAttrString(pModule, function.c_str());
  if (!pFunc || !PyCallable_Check(pFunc)) {
    std::cout << "PYTHON API ERROR: Function \"" << function
              << "\" does not exist.\n";
    PyEval_ReleaseThread(m_mainThreadState);
    return false;
  }
  pArgs = PyTuple_New(2);
  pValue = SWIG_NewPointerObj(
      SWIG_as_voidptr(design->getCompiler()->getErrorContainer()),
      SWIGTYPE_p_SURELOG__ErrorContainer, 0 | 0);
  PyTuple_SetItem(pArgs, 0, pValue);
  pValue = SWIG_NewPointerObj(SWIG_as_voidptr(design),
                              SWIGTYPE_p_SURELOG__Design, 0 | 0);
  PyTuple_SetItem(pArgs, 1, pValue);
  PyObject_CallObject(pFunc, pArgs);
  PyErr_Print();
  Py_DECREF(pArgs);
  Py_XDECREF(pFunc);
  Py_DECREF(pModule);

  PyEval_ReleaseThread(m_mainThreadState);
  return true;
}
