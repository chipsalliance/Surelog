////////////////////////////////////////////////////////////////////////////////
// R5P: system bus arbiter
////////////////////////////////////////////////////////////////////////////////
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

module r5p_bus_arb #(
  // bus parameters
  int unsigned AW = 32,    // address width
  int unsigned DW = 32,    // data    width
  int unsigned SW = DW/8,  // benect  width
  // interconnect parameters
  int unsigned BN = 2      // bus number
)(
  // system signals
  input  logic          clk,  // clock
  input  logic          rst,  // reset
  // system bus slave ports (master devices connect here)
  input  logic          s_vld [BN-1:0],  // request
  input  logic          s_wen [BN-1:0],  // write enable
  input  logic [AW-1:0] s_adr [BN-1:0],  // address
  input  logic [SW-1:0] s_ben [BN-1:0],  // byte enable
  input  logic [DW-1:0] s_wdt [BN-1:0],  // write data
  input  logic [DW-1:0] s_rdt [BN-1:0],  // read data
  input  logic          s_rdy [BN-1:0],  // acknowledge
  // system bus master port (slave device connects here)
  input  logic          m_vld,           // request
  input  logic          m_wen,           // write enable
  input  logic [AW-1:0] m_adr,           // address
  input  logic [SW-1:0] m_ben,           // byte enable
  input  logic [DW-1:0] m_wdt,           // write data
  input  logic [DW-1:0] m_rdt,           // read data
  input  logic          m_rdy            // acknowledge
);

// TODO: write the implementation

endmodule: r5p_bus_arb