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
 * File:   ParseCache.h
 * Author: alain
 *
 * Created on April 29, 2017, 4:20 PM
 */

#ifndef PARSECACHE_H
#define PARSECACHE_H


#include "flatbuffers/flatbuffers.h"
#include "parser_generated.h"
#include <cstdio> // For printing and file access.
#include "Cache.h"

namespace SURELOG {

class ParseCache : Cache {
public:
    ParseCache(ParseFile* pp);
    ParseCache(const ParseCache& orig);
    bool restore();
    bool save();
    bool isValid();
    virtual ~ParseCache();
private:
    ParseFile* m_parse;
    std::string getCacheFileName_(std::string fileName = "");
    bool restore_(std::string cacheFileName);
    bool checkCacheIsValid_(std::string cacheFileName);
    bool m_isPrecompiled;
};

};


#endif /* PARSECACHE_H */





