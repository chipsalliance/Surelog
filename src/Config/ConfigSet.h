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
 * File:   ConfigSet.h
 * Author: alain
 *
 * Created on February 10, 2018, 11:14 PM
 */

#ifndef CONFIGSET_H
#define CONFIGSET_H

#include <string_view>
#include <vector>

#include "Config/Config.h"

namespace SURELOG {

class ConfigSet final {
 public:
  void addConfig(const Config& config) { m_configs.emplace_back(config); }
  std::vector<Config>& getAllMutableConfigs() { return m_configs; }
  Config* getMutableConfigByName(std::string_view configName);

  // Are there places where we can return a non-mutable config ?

 private:
  std::vector<Config> m_configs;
};

}  // namespace SURELOG

#endif /* CONFIGSET_H */
