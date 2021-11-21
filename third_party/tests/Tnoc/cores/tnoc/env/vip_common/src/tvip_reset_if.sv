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
`ifndef TVIP_RESET_IF_SV
`define TVIP_RESET_IF_SV

`include  "tvip_common_macros.svh"

interface tvip_reset_if ();
  timeunit      1ns;
  timeprecision `TVIP_TIME_PRECISION;

  bit reset = 0;
  bit reset_n;

  assign  reset_n = ~reset;

  task automatic initiate(realtime duration_ns);
    reset = 1;
    #(duration_ns);
    reset = 0;
  endtask
endinterface
`endif
