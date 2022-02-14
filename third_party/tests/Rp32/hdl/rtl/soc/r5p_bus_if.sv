///////////////////////////////////////////////////////////////////////////////
// R5P: system bus SystemVerilog interface
///////////////////////////////////////////////////////////////////////////////
// Copyright 2022 Iztok Jeras
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
///////////////////////////////////////////////////////////////////////////////

interface r5p_bus_if #(
  int unsigned AW = 32,    // address width
  int unsigned DW = 32,    // data    width
  int unsigned BW = DW/8   // benect  width
)(
  // system signals
  input  logic clk,  // clock
  input  logic rst   // reset
);

// system bus
logic          vld;  // valid
logic          wen;  // write enable
logic [AW-1:0] adr;  // address
logic [BW-1:0] ben;  // byte enable
logic [DW-1:0] wdt;  // write data
logic [DW-1:0] rdt;  // read data
logic          rdy;  // ready

// manager
modport  man (
  // system signals
  input  clk,
  input  rst,
  // system bus
  output vld,
  output wen,
  output adr,
  output ben,
  output wdt,
  input  rdt,
  input  rdy
);

// subordinate
modport  sub (
  // system signals
  input  clk,
  input  rst,
  // system bus
  input  vld,
  input  wen,
  input  adr,
  input  ben,
  input  wdt,
  output rdt,
  output rdy
);

endinterface: r5p_bus_if