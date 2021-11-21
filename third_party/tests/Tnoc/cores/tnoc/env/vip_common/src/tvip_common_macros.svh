//------------------------------------------------------------------------------
//  Copyright 2017 Taichi Ishitani
//
//  Licensed under the Apache License, Version 2.0 (the "License");
//  you may not use this file except in compliance with the License.
//  You may obtain a copy of the License at
//
//  http://www.apache.org/licenses/LICENSE-2.0
//
//  Unless required by applicable law or agreed to in writing, software
//  distributed under the License is distributed on an "AS IS" BASIS,
//  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//  See the License for the specific language governing permissions and
//  limitations under the License.
//------------------------------------------------------------------------------
`ifndef TVIP_COMMON_MACROS_SVH
`define TVIP_COMMON_MACROS_SVH

`ifndef TVIP_TIME_PRECISION
  `define TVIP_TIME_PRECISION 1ps
`endif

`define tvip_delay_constraint(DELAY, CONFIGURATION) \
if (CONFIGURATION.max_delay > CONFIGURATION.min_delay) { \
  (DELAY inside {[CONFIGURATION.min_delay:CONFIGURATION.mid_delay[0]]}) || \
  (DELAY inside {[CONFIGURATION.mid_delay[1]:CONFIGURATION.max_delay]}); \
  if (CONFIGURATION.min_delay == 0) { \
    DELAY dist { \
      0                                                       := CONFIGURATION.weight_zero_delay, \
      [1                         :CONFIGURATION.mid_delay[0]] :/ CONFIGURATION.weight_short_delay, \
      [CONFIGURATION.mid_delay[1]:CONFIGURATION.max_delay   ] :/ CONFIGURATION.weight_long_delay \
    }; \
  } \
  else { \
    DELAY dist { \
      [CONFIGURATION.min_delay   :CONFIGURATION.mid_delay[0]] :/ CONFIGURATION.weight_short_delay, \
      [CONFIGURATION.mid_delay[1]:CONFIGURATION.max_delay   ] :/ CONFIGURATION.weight_long_delay \
    }; \
  } \
} \
else { \
  DELAY == CONFIGURATION.min_delay; \
}

`define tvip_array_delay_constraint(DELAY, CONFIGURATION) \
foreach (DELAY[__i]) { \
  `tvip_delay_constraint(DELAY[__i], CONFIGURATION) \
}

`endif
