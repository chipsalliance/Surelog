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
 * File:   PythonListen.h
 * Author: alain
 *
 * Created on June 4, 2017, 8:09 PM
 */

#ifndef PYTHONLISTEN_H
#define PYTHONLISTEN_H

namespace SURELOG {

class PythonListen {
public:
    PythonListen(ParseFile* parse, CompileSourceFile* m_compileSourceFile);
    PythonListen(const PythonListen& orig);
    bool listen();
    
    virtual ~PythonListen();
    
    CompileSourceFile* getCompileSourceFile() { return m_compileSourceFile; }
    ParseFile* getParseFile() { return m_parse; }
    
    void addError(Error& error);
    
private:
   ParseFile*            m_parse;
   CompileSourceFile*    m_compileSourceFile;
   std::vector<SV3_1aPythonListener*> m_pythonListeners;
   bool m_usingCachedVersion;
};

};

#endif /* PYTHONLISTEN_H */




