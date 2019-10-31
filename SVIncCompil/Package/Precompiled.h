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
 * File:   Precompiled.h
 * Author: alain
 *
 * Created on April 28, 2018, 10:27 AM
 */
#include <string>
#include <set>
#include <map>

#ifndef PRECOMPILED_H
#define PRECOMPILED_H

class Precompiled {
public:
    Precompiled();
    void addPrecompiled(std::string package_name, std::string fileName);
    
    static Precompiled* getSingleton();
    
    std::string getFileName(std::string packageName);
    bool isFilePrecompiled(std::string fileName);
    bool isPackagePrecompiled(std::string package);
    
    virtual ~Precompiled() {};
private:
    
    std::map<std::string, std::string> m_packageMap;
    std::set<std::string> m_packageFileSet;
    static Precompiled*   m_singleton;
};

#endif /* PRECOMPILED_H */


