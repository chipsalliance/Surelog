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
 * File:   SymbolTable.h
 * Author: alain
 *
 * Created on March 6, 2017, 11:10 PM
 */

#ifndef SYMBOLTABLE_H
#define SYMBOLTABLE_H
#include <string>
#include <map>
#include <unordered_map>
#include <vector>

namespace SURELOG {

typedef unsigned long SymbolId; // 64 bit

typedef unsigned int NodeId;    // 32 bit

#define InvalidNodeId 969696

class SymbolTable {
public:
    SymbolTable();
   // SymbolTable(const SymbolTable& orig);
    
    SymbolId registerSymbol(const std::string symbol);
    SymbolId getId(const std::string symbol);
    const std::string getSymbol(SymbolId id);
    const std::string getBadSymbol() { return m_badSymbol; }
    const SymbolId getBadId() { return m_badId; }
    virtual ~SymbolTable();
    
    static const std::string getEmptyMacroMarker() { return m_emptyMacroMarker; }
    std::vector<std::string>& getSymbols() { return m_id2SymbolMap; }
private:
    SymbolId m_idCounter;
    std::vector<std::string> m_id2SymbolMap;
    std::unordered_map<std::string, SymbolId> m_symbol2IdMap;
    static std::string m_badSymbol;
    static SymbolId    m_badId;
    static std::string m_emptyMacroMarker;
};

};

#endif /* SYMBOLTABLE_H */




