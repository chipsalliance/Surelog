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
 * File:   Waiver.cpp
 * Author: alain
 *
 * Created on May 7, 2017, 11:11 PM
 */
#include "ErrorReporting/Waiver.h"

#include <fstream>
#include <iostream>
#include <sstream>
#include <string>

#include "ErrorReporting/ErrorDefinition.h"

using namespace SURELOG;

std::set<std::string, std::less<>> Waiver::m_macroArgCheck;
std::multimap<ErrorDefinition::ErrorType, Waiver::WaiverData> Waiver::m_waivers;

// Example of message to waive:
// [WARNI:PP0113] ../../../UVM/uvm-1.2/src/macros/uvm_callback_defines.svh, line
// 294, col 8: Unused macro argument "CB".

void Waiver::setWaiver(std::string_view messageId, std::string_view fileName,
                       unsigned int line, std::string_view objectName) {
  ErrorDefinition::ErrorType type =
      ErrorDefinition::getErrorType(std::string(messageId));
  Waiver::WaiverData data(type, fileName, line, objectName);
  m_waivers.insert(std::make_pair(type, data));
}

void Waiver::initWaivers() { m_macroArgCheck.insert("vmm_sformatf"); }

bool Waiver::macroArgCheck(std::string_view name) {
  return (m_macroArgCheck.find(name) != m_macroArgCheck.end());
}
