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
 * File:   FileUtils.cpp
 * Author: alain
 *
 * Created on March 16, 2017, 11:02 PM
 */

#include <Surelog/Utils/FileUtils.h>

#include <algorithm>
#include <iostream>

namespace SURELOG {

namespace fs = std::filesystem;

std::string FileUtils::hashPath(const fs::path& path) {
  const std::string separator(1, fs::path::preferred_separator);
  std::string last_dir = path.string();
  while (!last_dir.empty() &&
         ((last_dir.back() == '/') || (last_dir.back() == '\\'))) {
    last_dir.pop_back();
  }
  std::size_t val = std::hash<std::string>{}(last_dir);
  if (!last_dir.empty()) {
    auto it1 = std::find_if(last_dir.rbegin(), last_dir.rend(),
                            [](char ch) { return (ch == '/' || ch == '\\'); });
    if (it1 != last_dir.rend()) last_dir.erase(last_dir.begin(), it1.base());
  }
  std::string hashedpath = last_dir + "_" + std::to_string(val) + separator;
  return hashedpath;
}

}  // namespace SURELOG
