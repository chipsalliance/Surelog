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
 * File:   Precompiled.cpp
 * Author: alain
 * 
 * Created on April 28, 2018, 10:27 AM
 */

#include "Precompiled.h"

Precompiled* Precompiled::m_singleton = NULL;
  
Precompiled::Precompiled () { 
   addPrecompiled("uvm_pkg","uvm_pkg.sv");  
   addPrecompiled("ovm_pkg","ovm_pkg.sv");  
}

Precompiled* Precompiled::getSingleton() {
  if (m_singleton == NULL)
    m_singleton = new Precompiled();
  return m_singleton;
}

void Precompiled::addPrecompiled(std::string packageName, std::string fileName) {
  m_packageMap.insert(std::make_pair(packageName,fileName));  
  m_packageFileSet.insert(fileName);
}
    
    
std::string Precompiled::getFileName(std::string packageName) {
  auto itr = m_packageMap.find(packageName);
  if (itr == m_packageMap.end()) 
    {
      return "";
    }
  else 
    {
      return (*itr).second;
    }
}

bool Precompiled::isFilePrecompiled(std::string fileName) {
  auto itr = m_packageFileSet.find(fileName);
  if (itr == m_packageFileSet.end())
    {
      return false;
    }
  else 
    {
      return true;
    }
}

bool Precompiled::isPackagePrecompiled(std::string packageName) {
  auto itr = m_packageMap.find(packageName);
  if (itr == m_packageMap.end()) 
    {
      return false;
    }
  else 
    {
      return true;
    }
}
      
