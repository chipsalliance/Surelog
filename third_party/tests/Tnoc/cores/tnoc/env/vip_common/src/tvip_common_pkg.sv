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
`ifndef TVIP_COMMON_PKG_SV
`define TVIP_COMMON_PKG_SV

`include  "tvip_common_macros.svh"

`include  "tvip_clock_if.sv"
`include  "tvip_reset_if.sv"

package tvip_common_pkg;
  import  uvm_pkg::*;
  import  tue_pkg::*;

  `include  "uvm_macros.svh"
  `include  "tue_macros.svh"

  `include  "tvip_common_types.svh"
  `include  "tvip_common_item.svh"
  `include  "tvip_delay_configuration.svh"
  `include  "tvip_memory.svh"
  `include  "tvip_item_waiter.svh"
endpackage
`endif
