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
 * File:   Error.cpp
 * Author: alain
 *
 * Created on March 5, 2017, 11:30 PM
 */

#include "ErrorReporting/Error.h"

using namespace SURELOG;

Error::Error(ErrorDefinition::ErrorType errorId, Location& loc,
             std::vector<Location>* extraLocs)
    : m_errorId(errorId), m_reported(false), m_waived(false) {
  m_locations.push_back(loc);
  if (extraLocs) {
    for (auto loc : (*extraLocs)) m_locations.push_back(loc);
  }
}

Error::Error(ErrorDefinition::ErrorType errorId, Location& loc, Location& extra)
    : m_errorId(errorId), m_reported(false), m_waived(false) {
  m_locations.push_back(loc);
  m_locations.push_back(extra);
}

Error::Error(ErrorDefinition::ErrorType errorId,
             std::vector<Location>& locations)
    : m_errorId(errorId), m_reported(false), m_waived(false) {
  for (auto loc : (locations)) m_locations.push_back(loc);
}

bool Error::operator==(const Error& rhs) const {
  if (m_errorId != rhs.m_errorId) return false;
  if (m_locations.size() < rhs.m_locations.size())
    return std::equal(m_locations.begin(), m_locations.end(),
                      rhs.m_locations.begin());
  else
    return std::equal(rhs.m_locations.begin(), rhs.m_locations.end(),
                      m_locations.begin());
}

bool Error::operator<(const Error& rhs) const {
  if (m_errorId < rhs.m_errorId) return true;
  if (m_locations.size() < rhs.m_locations.size()) return true;
  if (m_reported != rhs.m_reported) return false;
  if (m_waived != rhs.m_waived) return false;
  for (unsigned int i = 0; i < m_locations.size(); i++) {
    if (m_locations[i] < rhs.m_locations[i]) return true;
  }
  return false;
}

Error::~Error() {}
