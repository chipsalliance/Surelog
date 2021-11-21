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
`ifndef TUE_VERSION_DEFINES_SVH
`define TUE_VERSION_DEFINES_SVH

`define TUE_MAJOR_REV 0

`define TUE_MINOR_REV 1

`define TUE_NAME  TUE

`define TUE_VERSION_STRING `"`TUE_NAME``-```TUE_MAJOR_REV``.```TUE_MINOR_REV```"

`ifdef UVM_VERSION_1_0
  `define TUE_UVM_PRE_IEEE
`elsif UVM_VERSION_1_1
  `define TUE_UVM_PRE_IEEE
`elsif UVM_VERSION_1_2
  `define TUE_UVM_PRE_IEEE
`endif

`endif
