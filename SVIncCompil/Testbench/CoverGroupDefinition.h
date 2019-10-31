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
 * File:   CoverGroupDefinition.h
 * Author: alain
 *
 * Created on March 20, 2019, 9:06 PM
 */

#ifndef COVERGROUPDEFINITION_H
#define COVERGROUPDEFINITION_H

#include "../SourceCompile/SymbolTable.h"
#include "../Design/FileContent.h"
#include "../SourceCompile/VObjectTypes.h"

namespace SURELOG {

    class CoverGroupDefinition {
    public:

        CoverGroupDefinition(FileContent* fC, NodeId id, std::string name) : m_fileContent(fC), m_nodeId(id), m_name(name) {
        }

        std::string getName() {
            return m_name;
        }

        FileContent* getFileContent() {
            return m_fileContent;
        }

        NodeId getNodeId() {
            return m_nodeId;
        }

        virtual ~CoverGroupDefinition();
    private:
        FileContent* m_fileContent;
        NodeId m_nodeId;
        std::string m_name;
    };

};

#endif /* COVERGROUPDEFINITION_H */



