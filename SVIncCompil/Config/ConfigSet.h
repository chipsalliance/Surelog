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
#include "Config.h"
#include <vector>

namespace SURELOG {

class ConfigSet {
 public:
  ConfigSet() {}
  virtual ~ConfigSet();
  void addConfig(Config& config) { m_configs.push_back(config); }
  std::vector<Config>& getAllConfigs() { return m_configs; }
  Config* getConfig(std::string configName);

 private:
  std::vector<Config> m_configs;
};

};  // namespace SURELOG

#endif /* CONFIGSET_H */
