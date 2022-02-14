///////////////////////////////////////////////////////////////////////////////
// R5P: general purpose registers
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

module r5p_gpr #(
  int unsigned AW   = 5,     // can be 4 for RV32E base ISA
  int unsigned XLEN = 32,    // XLEN width
  bit          WBYP = 1'b0,  // write bypass
  // implementation device (ASIC/FPGA vendor/device)
  string       CHIP = ""
)(
  // system signals
  input  logic            clk,  // clock
  input  logic            rst,  // reset
  // read/write enable
  input  logic            e_rs1,
  input  logic            e_rs2,
  input  logic            e_rd,
  // read/write address
  input  logic   [AW-1:0] a_rs1,
  input  logic   [AW-1:0] a_rs2,
  input  logic   [AW-1:0] a_rd,
  // read/write data
  output logic [XLEN-1:0] d_rs1,
  output logic [XLEN-1:0] d_rs2,
  input  logic [XLEN-1:0] d_rd
);

// local signals
logic            wen;
logic [XLEN-1:0] t_rs1;
logic [XLEN-1:0] t_rs2;

// special handling of x0
assign wen = e_rd & |a_rd;

generate
if (CHIP == "ARTIX_XPM") begin: gen_artix_xpm

  // xpm_memory_dpdistram: Dual Port Distributed RAM
  // Xilinx Parameterized Macro, version 2021.2
  xpm_memory_dpdistram #(
    .ADDR_WIDTH_A            (AW),             // DECIMAL
    .ADDR_WIDTH_B            (AW),             // DECIMAL
    .BYTE_WRITE_WIDTH_A      (XLEN),           // DECIMAL
    .CLOCKING_MODE           ("common_clock"), // String
    .MEMORY_INIT_FILE        ("none"),         // String
    .MEMORY_INIT_PARAM       ("0"),            // String
    .MEMORY_OPTIMIZATION     ("true"),         // String
    .MEMORY_SIZE             (XLEN * 2**AW),   // DECIMAL
    .MESSAGE_CONTROL         (0),              // DECIMAL
    .READ_DATA_WIDTH_A       (XLEN),           // DECIMAL
    .READ_DATA_WIDTH_B       (XLEN),           // DECIMAL
    .READ_LATENCY_A          (1),              // DECIMAL (registered, port is not used)
    .READ_LATENCY_B          (0),              // DECIMAL (combinational)
    .READ_RESET_VALUE_A      ("0"),            // String
    .READ_RESET_VALUE_B      ("0"),            // String
    .RST_MODE_A              ("SYNC"),         // String
    .RST_MODE_B              ("SYNC"),         // String
    .SIM_ASSERT_CHK          (0),              // DECIMAL; 0=disable simulation messages, 1=enable simulation messages
    .USE_EMBEDDED_CONSTRAINT (0),              // DECIMAL
    .USE_MEM_INIT            (1),              // DECIMAL
    .USE_MEM_INIT_MMI        (0),              // DECIMAL
    .WRITE_DATA_WIDTH_A      (XLEN)            // DECIMAL
  ) gpr [2:1] (
    .douta   (),
    .doutb   ({t_rs2, t_rs1}),
    .addra   (a_rd),
    .addrb   ({a_rs2, a_rs1}),
    .clka    (clk),
    .clkb    (clk),
    .dina    (d_rd),
    .ena     (1'b1),
    .enb     (1'b1),
    .regcea  (1'b1),
    .regceb  (1'b1),
    .rsta    (rst),
    .rstb    (rst),
    .wea     (wen)
  );

end: gen_artix_xpm
else if (CHIP == "ARTIX_GEN") begin: gen_artix_gen

  dist_mem_gen_0 gpr [2:1] (
    .clk   (clk),
    .we    (wen),
    .a     (a_rd),
    .d     (d_rd),
    .dpra  ({a_rs2, a_rs1}),
    .dpo   ({t_rs2, t_rs1})
  );

end: gen_artix_gen
else if (CHIP == "CYCLONE_V") begin: gen_cyclone_v

  gpr32x32 gpr [2:1] (
    // write access
    .clock      (clk),
    .wren       (wen),
    .wraddress  (a_rd),
    .data       (d_rd),
    // read access
    .rdaddress  ({a_rs2, a_rs1}),
    .q          ({t_rs2, t_rs1})
  );

end: gen_cyclone_v
else if (CHIP == "ECP5") begin: gen_ecp5

  // file:///usr/local/diamond/3.12/docs/webhelp/eng/index.htm#page/Reference%20Guides/IPexpress%20Modules/pmi_distributed_dpram.htm#
  pmi_distributed_dpram #(
    .pmi_addr_depth       (32),
    .pmi_addr_width       (5),
    .pmi_data_width       (XLEN),
    .pmi_regmode          ("noreg"),
    .pmi_init_file        ("none"),
    .pmi_init_file_format ("binary"),
    .pmi_family           ("ECP5")
  ) gpr [2:1] (
    // write access
    .WrClock    (clk),
    .WrClockEn  (1'b1),
    .WE         (wen),
    .WrAddress  (a_rd),
    .Data       (d_rd),
    // read access
    .RdClock    (clk),
    .RdClockEn  (1'b1),
    .Reset      (1'b0),
    .RdAddress  ({a_rs2, a_rs1}),
    .Q          ({t_rs2, t_rs1})
  );

end: gen_ecp5
else begin: gen_default

  // register file (FPGA would initialize it to all zeros)
  logic [XLEN-1:0] gpr [0:2**AW-1] = '{default: '0};

  // write access
  always_ff @(posedge clk)
  if (wen)  gpr[a_rd] <= d_rd;

  // read access
  assign t_rs1 = gpr[a_rs1];
  assign t_rs2 = gpr[a_rs2];

end: gen_default
endgenerate

generate
if (WBYP) begin: gen_wb_bypass

  assign d_rs1 = (wen & (a_rd == a_rs1)) ? d_rd : t_rs1;
  assign d_rs2 = (wen & (a_rd == a_rs2)) ? d_rd : t_rs2;

end: gen_wb_bypass
else begin: gen_wb_default

  assign d_rs1 = t_rs1;
  assign d_rs2 = t_rs2;

end: gen_wb_default
endgenerate

endmodule: r5p_gpr