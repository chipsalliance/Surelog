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
 * File:   Waiver.h
 * Author: alain
 *
 * Created on May 7, 2017, 11:11 PM
 */

#ifndef WAIVER_H
#define WAIVER_H

#include <map>
#include <set>
#include <string>
#include <string_view>
#include <vector>

#include "ErrorReporting/ErrorDefinition.h"

namespace SURELOG {

class Waiver final {
 public:
  static void initWaivers();

  static bool macroArgCheck(const std::string& name);

  static void setWaiver(const std::string& messageId,
                        const std::string& fileName, unsigned int line,
                        const std::string& objectName);

  class WaiverData {
   public:
    WaiverData(ErrorDefinition::ErrorType messageId, std::string_view fileName,
               unsigned int line, std::string_view objectName)
        : m_messageId(messageId),
          m_fileName(fileName),
          m_line(line),
          m_objectId(objectName) {}
    const ErrorDefinition::ErrorType m_messageId;
    const std::string m_fileName;
    const unsigned int m_line;
    const std::string m_objectId;
  };

  static std::multimap<ErrorDefinition::ErrorType, WaiverData>& getWaivers() {
    return m_waivers;
  }

 private:
  Waiver() = delete;
  Waiver(const Waiver& orig) = delete;

  static std::set<std::string> m_macroArgCheck;
  static std::multimap<ErrorDefinition::ErrorType, WaiverData> m_waivers;
};

}  // namespace SURELOG

#endif /* WAIVER_H */
