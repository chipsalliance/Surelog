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
 * File:   MacroInfo.h
 * Author: alain
 *
 * Created on April 5, 2017, 11:46 PM
 */

#ifndef MACROINFO_H
#define MACROINFO_H

#include <string>
#include <vector>
#include <map>
namespace SURELOG {

class MacroInfo {
 public:
  MacroInfo(std::string name, int type, SymbolId file, unsigned int line,
            unsigned short int column,
            const std::vector<std::string>& arguments,
            const std::vector<std::string>& tokens)
      : m_name(name),
        m_type(type),
        m_file(file),
        m_line(line),
        m_column(column),
        m_arguments(arguments),
        m_tokens(tokens) {}
  enum Type {
    NO_ARGS,
    WITH_ARGS,
  };
  std::string m_name;
  int m_type;
  SymbolId m_file;
  unsigned int m_line;
  unsigned short int m_column;
  std::vector<std::string> m_arguments;
  std::vector<std::string> m_tokens;
};

typedef std::map<std::string, MacroInfo*> MacroStorage;
typedef std::map<std::string, MacroInfo*> MacroStorageRef;

};  // namespace SURELOG

#endif /* MACROINFO_H */
