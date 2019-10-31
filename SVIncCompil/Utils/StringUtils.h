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
 * File:   StringUtils.h
 * Author: alain
 *
 * Created on March 14, 2017, 10:43 PM
 */

#ifndef STRINGUTILS_H
#define STRINGUTILS_H
#include <string>
#include <vector>

namespace SURELOG {

class StringUtils {
public:
    static void tokenize(std::string str, std::string separators, std::vector<std::string>& args);
    static void tokenizeMulti(std::string str, std::string multichar_separator, std::vector<std::string>& args);
    static void tokenizeBalanced(std::string str, std::string separator, std::vector<std::string>& args);
    static void replaceInTokenVector(std::vector<std::string>& tokens, std::vector<std::string> pattern, std::string news);
    static void replaceInTokenVector(std::vector<std::string>& tokens, std::string pattern, std::string news);
    static std::string getFirstNonEmptyToken(std::vector<std::string>& tokens);
    
    static std::string & trim(std::string & str);
    static std::string & ltrim(std::string & str);
    static std::string & ltrim(std::string & str, char c);
    static bool ltrimStat(std::string & str, char c);
    static std::string & rtrim(std::string & str);
    static std::string & rtrimEqual(std::string & str);
    static std::string & rtrim(std::string & str, char c);
    static std::string   leaf(std::string str);
    
    static std::string & getRootFileName(std::string & str);
    static std::string   eliminateRelativePath(std::string path);
    static std::string   replaceAll(std::string str, const std::string& from, const std::string& to);
    static std::string   getLineInString(std::string& bulk, unsigned int line);
    
    static std::string to_string(double a_value, const int n = 3);
    
private:
    StringUtils();
    StringUtils(const StringUtils& orig);
    virtual ~StringUtils();
private:

};

};

#endif /* STRINGUTILS_H */




