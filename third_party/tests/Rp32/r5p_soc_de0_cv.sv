// ============================================================================
// Copyright (c) 2014 by Terasic Technologies Inc.
// ============================================================================
//
// Permission:
//
//   Terasic grants permission to use and modify this code for use
//   in synthesis for all Terasic Development Boards and Altera Development
//   Kits made by Terasic.  Other use of this code, including the selling
//   ,duplication, or modification of any portion is strictly prohibited.
//
// Disclaimer:
//
//   This VHDL/Verilog or C/C++ source code is intended as a design reference
//   which illustrates how these types of functions can be implemented.
//   It is the user's responsibility to verify their design for
//   consistency and functionality through the use of formal
//   verification methods.  Terasic provides no warranty regarding the use
//   or functionality of this code.
//
// ============================================================================
//
//  Terasic Technologies Inc
//  9F., No.176, Sec.2, Gongdao 5th Rd, East Dist, Hsinchu City, 30070. Taiwan
//
//
//                     web: http://www.terasic.com/
//                     email: support@terasic.com
//
// ============================================================================
//   Ver  :| Author            :| Mod. Date :| Changes Made:
//   V1.0 :| Yue Yang          :| 08/25/2014:| Initial Revision
// ============================================================================

//`define Enable_CLOCK2
//`define Enable_CLOCK3
//`define Enable_CLOCK4
`define Enable_CLOCK
//`define Enable_DRAM
`define Enable_GPIO
//`define Enable_HEX0
//`define Enable_HEX1
//`define Enable_HEX2
//`define Enable_HEX3
//`define Enable_HEX4
//`define Enable_HEX5
//`define Enable_KEY
//`define Enable_LEDR
//`define Enable_PS2
`define Enable_RESET
//`define Enable_SD
//`define Enable_SW
//`define Enable_VGA

module r5p_soc_de0_cv (

`ifdef Enable_CLOCK2
      ///////// CLOCK2 "3.3-V LVTTL" /////////
      input              CLOCK2_50,
`endif

`ifdef Enable_CLOCK3
      ///////// CLOCK3 "3.3-V LVTTL" /////////
      input              CLOCK3_50,
`endif

`ifdef Enable_CLOCK4
      ///////// CLOCK4  "3.3-V LVTTL"  /////////
      inout              CLOCK4_50,
`endif
`ifdef Enable_CLOCK
      ///////// CLOCK  "3.3-V LVTTL" /////////
      input              CLOCK_50,
`endif
`ifdef Enable_DRAM
      ///////// DRAM  "3.3-V LVTTL" /////////
      output      [12:0] DRAM_ADDR,
      output      [1:0]  DRAM_BA,
      output             DRAM_CAS_N,
      output             DRAM_CKE,
      output             DRAM_CLK,
      output             DRAM_CS_N,
      inout       [15:0] DRAM_DQ,
      output             DRAM_LDQM,
      output             DRAM_RAS_N,
      output             DRAM_UDQM,
      output             DRAM_WE_N,
`endif
`ifdef Enable_GPIO
      ///////// GPIO "3.3-V LVTTL" /////////
      inout       [35:0] GPIO_0,
      inout       [35:0] GPIO_1,
`endif
`ifdef Enable_HEX0
      ///////// HEX0  "3.3-V LVTTL" /////////
      output      [6:0]  HEX0,
`endif
`ifdef Enable_HEX1
      ///////// HEX1 "3.3-V LVTTL" /////////
      output      [6:0]  HEX1,
`endif
`ifdef Enable_HEX2
      ///////// HEX2 "3.3-V LVTTL" /////////
      output      [6:0]  HEX2,
`endif
`ifdef Enable_HEX3
      ///////// HEX3 "3.3-V LVTTL" /////////
      output      [6:0]  HEX3,
`endif
`ifdef Enable_HEX4
      ///////// HEX4 "3.3-V LVTTL" /////////
      output      [6:0]  HEX4,
`endif
`ifdef Enable_HEX5
      ///////// HEX5 "3.3-V LVTTL" /////////
      output      [6:0]  HEX5,
`endif
`ifdef Enable_KEY
      ///////// KEY  "3.3-V LVTTL" /////////
      input       [3:0]  KEY,
`endif
`ifdef Enable_LEDR
      ///////// LEDR /////////
      output      [9:0]  LEDR,
`endif
`ifdef Enable_PS2
      ///////// PS2 "3.3-V LVTTL" /////////
      inout              PS2_CLK,
      inout              PS2_CLK2,
      inout              PS2_DAT,
      inout              PS2_DAT2,
`endif
`ifdef Enable_RESET
      ///////// RESET "3.3-V LVTTL" /////////
      input              RESET_N
`endif
`ifdef Enable_SD
      ///////// SD "3.3-V LVTTL" /////////
      output             SD_CLK,
      inout              SD_CMD,
      inout       [3:0]  SD_DATA,
`endif
`ifdef Enable_SW
      ///////// SW "3.3-V LVTTL"/////////
      input       [9:0]  SW,
`endif
`ifdef Enable_VGA
      ///////// VGA  "3.3-V LVTTL" /////////
      output      [3:0]  VGA_B,
      output      [3:0]  VGA_G,
      output             VGA_HS,
      output      [3:0]  VGA_R,
      output             VGA_VS
`endif
);

///////////////////////////////////////////////////////////////////////////////
// local parameters
////////////////////////////////////////////////////////////////////////////////

//localparam int unsigned GW = 32;
localparam int unsigned GW = 1;

///////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

// clock
logic clk;

// reset synchronizer
logic rst;

// GPIO
logic [GW-1:0] gpio_o;
logic [GW-1:0] gpio_e;
logic [GW-1:0] gpio_i;

///////////////////////////////////////////////////////////////////////////////
// PLL
////////////////////////////////////////////////////////////////////////////////

// TODO: use proper PLL
assign clk = CLOCK_50;

///////////////////////////////////////////////////////////////////////////////
// reset synchronizer
////////////////////////////////////////////////////////////////////////////////

logic rst_r;

always @(posedge clk, negedge RESET_N)
if (~RESET_N)  {rst, rst_r} <= 2'b1;
else           {rst, rst_r} <= {rst_r, 1'b0};

////////////////////////////////////////////////////////////////////////////////
// R5P SoC instance
////////////////////////////////////////////////////////////////////////////////

r5p_soc_top #(
  .GW    (GW),
  .CHIP  ("CYCLONE_V")
) soc (
  // system signals
  .clk     (clk),
  .rst     (rst),
  // GPIO
  .gpio_o  (gpio_o),
  .gpio_e  (gpio_e),
  .gpio_i  (gpio_i)
);

////////////////////////////////////////////////////////////////////////////////
// GPIO
////////////////////////////////////////////////////////////////////////////////

// GPIO inputs
assign gpio_i = GPIO_0[GW-1:0];

// GPIO outputs
genvar i;
generate
for (i=0; i<GW; i++) begin: gen_gpio
  assign GPIO_0[i] = gpio_e[i] ? gpio_o[i] : 1'bz;
end: gen_gpio
endgenerate

// unused GPIO
assign GPIO_0[35:GW] = 'z;
assign GPIO_1[35:00] = 'z;

endmodule: r5p_soc_de0_cv
