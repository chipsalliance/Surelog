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
 * File:   ParseLibraryDef.h
 * Author: alain
 *
 * Created on January 27, 2018, 5:05 PM
 */

#ifndef PARSELIBRARYDEF_H
#define PARSELIBRARYDEF_H
#include "LibrarySet.h"
#include "../Config/ConfigSet.h"
#include "../Design/FileContent.h"

namespace SURELOG {

    class ParseLibraryDef {
    public:
        ParseLibraryDef(CommandLineParser* commandLineParser, ErrorContainer* errors, SymbolTable* symbolTable, LibrarySet* librarySet, ConfigSet* configSet);
        ParseLibraryDef(const ParseLibraryDef& orig);
        bool parseLibrariesDefinition();
        bool parseLibraryDefinition(SymbolId file, Library* lib = NULL);
        bool parseConfigDefinition();
        virtual ~ParseLibraryDef();
        SymbolId getFileId() { return m_fileId; }
        CommandLineParser* getCommandLineParser() {
            return m_commandLineParser;
        }

        ErrorContainer* getErrorContainer() {
            return m_errors;
        }

        SymbolTable* getSymbolTable() {
            return m_symbolTable;
        }

        LibrarySet* getLibrarySet() {
            return m_librarySet;
        }

        ConfigSet* getConfigSet() {
            return m_configSet;
        }
        
    private:
        SymbolId m_fileId;
        CommandLineParser* m_commandLineParser;
        ErrorContainer* m_errors;
        SymbolTable* m_symbolTable;
        LibrarySet* m_librarySet;
        ConfigSet*  m_configSet;
        FileContent* m_fileContent;
    };

};

#endif /* PARSELIBRARYDEF_H */


