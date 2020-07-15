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
 * File:   Error.h
 * Author: alain
 *
 * Created on March 5, 2017, 11:30 PM
 */

#ifndef ERROR_H
#define ERROR_H
#include "ErrorReporting/ErrorDefinition.h"
#include <string>
#include <vector>
#include "ErrorReporting/Location.h"

namespace SURELOG {

class ErrorContainer;

class Error final {
public:
  friend ErrorContainer;

  Error(ErrorDefinition::ErrorType errorId, const Location& loc,
        const std::vector<Location>* extraLocs = nullptr);
  Error(ErrorDefinition::ErrorType errorId,
        const Location& loc, const Location& extra);
  Error(ErrorDefinition::ErrorType errorId,
        const std::vector<Location>& locations);
  Error(const Error& orig) = default;

  bool operator==(const Error& rhs) const;
  bool operator<(const Error& rhs) const;
  struct compare {
    bool operator()(const Error& e1, const Error& e2) const { return e1 < e2; }
  };

  const std::vector<Location>& getLocations() const { return m_locations; }
  ErrorDefinition::ErrorType getType() const { return m_errorId; }

private:
  std::vector<Location> m_locations;
  ErrorDefinition::ErrorType m_errorId;
  bool m_reported = false;
  bool m_waived = false;
};

}  // namespace SURELOG

#endif /* ERROR_H */
