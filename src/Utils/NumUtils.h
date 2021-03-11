/*
 Copyright 2020 Alain Dargelas

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
 * File:   NumUtils.h
 * Author: alain
 *
 * Created on Dec 29, 2020, 10:43 PM
 */

#ifndef NUMUTILS_H
#define NUMUTILS_H

#include <map>
#include <string>
#include <string_view>
#include <vector>

namespace SURELOG {

class NumUtils {
 public:

  static std::string hexToBin(const std::string &s);
  
  static std::string binToHex(const std::string &s);

  static std::string toBinary(unsigned int size, uint64_t val);

 private:
  NumUtils() = delete;
  NumUtils(const NumUtils& orig) = delete;
  ~NumUtils() = delete;

 private:
};

};  // namespace SURELOG

#endif /* NUMUTILS_H */
