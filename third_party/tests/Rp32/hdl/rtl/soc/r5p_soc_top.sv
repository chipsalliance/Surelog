////////////////////////////////////////////////////////////////////////////////
// R5P: SoC
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

import riscv_isa_pkg::*;

module r5p_soc_top #(
  // GPIO
  int unsigned GW = 32,
  // RISC-V ISA
  int unsigned XLEN = 32,   // is used to quickly switch between 32 and 64 for testing
`ifndef SYNOPSYS_VERILOG_COMPILER
  // extensions  (see `riscv_isa_pkg` for enumeration definition)
  isa_ext_t    XTEN = RV_M | RV_C | RV_Zicsr,
  // privilige modes
  isa_priv_t   MODES = MODES_M,
  // ISA
//isa_t        ISA = XLEN==32 ? '{spec: '{base: RV_32I , ext: XTEN}, priv: MODES}
//                 : XLEN==64 ? '{spec: '{base: RV_64I , ext: XTEN}, priv: MODES}
//                            : '{spec: '{base: RV_128I, ext: XTEN}, priv: MODES},
  isa_t ISA = '{spec: RV32I, priv: MODES_NONE},
`endif
  // instruction bus
  int unsigned IAW = 14,    // instruction address width (byte address)
  int unsigned IDW = 32,    // instruction data    width
  // data bus
  int unsigned DAW = 15,    // data address width (byte address)
  int unsigned DDW = XLEN,  // data data    width
  int unsigned DBW = DDW/8, // data byte en width
  // instruction memory size (in bytes) and initialization file name
  int unsigned IMS = (IDW/8)*(2**IAW),
  string       IFN = "mem_if.vmem",
  // data memory size (in bytes)
  int unsigned DMS = (DDW/8)*(2**DAW),
  // implementation device (ASIC/FPGA vendor/device)
  string       CHIP = ""
)(
  // system signals
  input  logic          clk,  // clock
  input  logic          rst,  // reset (active low)
  // GPIO
  output logic [GW-1:0] gpio_o,
  output logic [GW-1:0] gpio_e,
  input  logic [GW-1:0] gpio_i
);

`ifdef SYNOPSYS_VERILOG_COMPILER
parameter isa_t ISA = '{spec: RV32I, priv: MODES_NONE};
`endif

///////////////////////////////////////////////////////////////////////////////
// local parameters and checks
////////////////////////////////////////////////////////////////////////////////

// in this SoC the data address space is split in half between memory and peripherals
localparam int unsigned RAW = DAW-1;

// TODO: check if instruction address bus width and instruction memory size fit
// TODO: check if data address bus width and data memory size fit

///////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

// system busses
r5p_bus_if #(.AW (IAW), .DW (IDW)) bus_if        (.clk (clk), .rst (rst));
r5p_bus_if #(.AW (DAW), .DW (DDW)) bus_ls        (.clk (clk), .rst (rst));
r5p_bus_if #(.AW (DAW), .DW (DDW)) bus_mem [1:0] (.clk (clk), .rst (rst));

////////////////////////////////////////////////////////////////////////////////
// R5P core instance
////////////////////////////////////////////////////////////////////////////////

r5p_core #(
  // RISC-V ISA
  .XLEN (XLEN),
  .ISA  (ISA),
  // instruction bus
  .IAW  (IAW),
  .IDW  (IDW),
  // data bus
  .DAW  (DAW),
  .DDW  (DDW),
  // implementation device (ASIC/FPGA vendor/device)
  .CHIP (CHIP)
) core (
  // system signals
  .clk     (clk),
  .rst     (rst),
  // instruction fetch
  .if_vld  (bus_if.vld),
  .if_adr  (bus_if.adr),
  .if_rdt  (bus_if.rdt),
  .if_rdy  (bus_if.rdy),
  // data load/store
  .ls_vld  (bus_ls.vld),
  .ls_wen  (bus_ls.wen),
  .ls_adr  (bus_ls.adr),
  .ls_ben  (bus_ls.ben),
  .ls_wdt  (bus_ls.wdt),
  .ls_rdt  (bus_ls.rdt),
  .ls_rdy  (bus_ls.rdy)
);

assign bus_if.wen = 1'b0;
assign bus_if.ben = '1;
assign bus_if.wdt = 'x;

////////////////////////////////////////////////////////////////////////////////
// load/store bus decoder
////////////////////////////////////////////////////////////////////////////////

r5p_bus_dec #(
  .AW  (DAW),
  .DW  (DDW),
  .BN  (2),                    // bus number
  .AS  ({ {1'b1, 14'hxxxx} ,   // 0x00_0000 ~ 0x1f_ffff - data memory
          {1'b0, 14'hxxxx} })  // 0x20_0000 ~ 0x2f_ffff - controller
) ls_dec (
  .s  (bus_ls      ),
  .m  (bus_mem[1:0])
);

////////////////////////////////////////////////////////////////////////////////
// memory
////////////////////////////////////////////////////////////////////////////////

generate
if (CHIP == "ARTIX_XPM") begin: gen_artix_xpm

  // xpm_memory_spram: Single Port RAM
  // Xilinx Parameterized Macro, version 2021.2
  xpm_memory_spram #(
    .ADDR_WIDTH_A        (IAW-2),           // DECIMAL
    .AUTO_SLEEP_TIME     (0),               // DECIMAL
    .BYTE_WRITE_WIDTH_A  (8),               // DECIMAL
    .CASCADE_HEIGHT      (0),               // DECIMAL
    .ECC_MODE            ("no_ecc"),        // String
    .MEMORY_INIT_FILE    ("imem.mem"),      // String
    .MEMORY_INIT_PARAM   (""),              // String
    .MEMORY_OPTIMIZATION ("true"),          // String
    .MEMORY_PRIMITIVE    ("auto"),          // String
    .MEMORY_SIZE         (8 * 2**IAW),      // DECIMAL
    .MESSAGE_CONTROL     (0),               // DECIMAL
    .READ_DATA_WIDTH_A   (IDW),             // DECIMAL
    .READ_LATENCY_A      (1),               // DECIMAL
    .READ_RESET_VALUE_A  ("0"),             // String
    .RST_MODE_A          ("SYNC"),          // String
    .SIM_ASSERT_CHK      (0),               // DECIMAL; 0=disable simulation messages, 1=enable simulation messages
    .USE_MEM_INIT        (1),               // DECIMAL
    .USE_MEM_INIT_MMI    (0),               // DECIMAL
    .WAKEUP_TIME         ("disable_sleep"), // String
    .WRITE_DATA_WIDTH_A  (IDW),             // DECIMAL
    .WRITE_MODE_A        ("read_first"),    // String
    .WRITE_PROTECT       (1)                // DECIMAL
  ) imem (
    // unused control/status signals
    .injectdbiterra (1'b0),
    .injectsbiterra (1'b0),
    .dbiterra       (),
    .sbiterra       (),
    .sleep          (1'b0),
    .regcea         (1'b1),
    // system bus
    .clka   (   bus_if.clk),
    .rsta   (   bus_if.rst),
    .ena    (   bus_if.vld),
    .wea    ({4{bus_if.wen}}),
    .addra  (   bus_if.adr[IAW-1:2]),
    .dina   (   bus_if.wdt),
    .douta  (   bus_if.rdt)
  );

  assign bus_if.rdy = 1'b1;

  // xpm_memory_spram: Single Port RAM
  // Xilinx Parameterized Macro, version 2021.2
  xpm_memory_spram #(
    .ADDR_WIDTH_A        (RAW-$clog2(DBW)),   // DECIMAL
    .AUTO_SLEEP_TIME     (0),                 // DECIMAL
    .BYTE_WRITE_WIDTH_A  (8),                 // DECIMAL
    .CASCADE_HEIGHT      (0),                 // DECIMAL
    .ECC_MODE            ("no_ecc"),          // String
    .MEMORY_INIT_FILE    ("none"),            // String
    .MEMORY_INIT_PARAM   ("0"),               // String
    .MEMORY_OPTIMIZATION ("true"),            // String
    .MEMORY_PRIMITIVE    ("auto"),            // String
    .MEMORY_SIZE         (8 * 2**RAW),        // DECIMAL
    .MESSAGE_CONTROL     (0),                 // DECIMAL
    .READ_DATA_WIDTH_A   (DDW),               // DECIMAL
    .READ_LATENCY_A      (1),                 // DECIMAL
    .READ_RESET_VALUE_A  ("0"),               // String
    .RST_MODE_A          ("SYNC"),            // String
    .SIM_ASSERT_CHK      (0),                 // DECIMAL; 0=disable simulation messages, 1=enable simulation messages
    .USE_MEM_INIT        (1),                 // DECIMAL
    .USE_MEM_INIT_MMI    (0),                 // DECIMAL
    .WAKEUP_TIME         ("disable_sleep"),   // String
    .WRITE_DATA_WIDTH_A  (DDW),               // DECIMAL
    .WRITE_MODE_A        ("read_first"),      // String
    .WRITE_PROTECT       (1)                  // DECIMAL
  ) dmem (
    // unused control/status signals
    .injectdbiterra (1'b0),
    .injectsbiterra (1'b0),
    .dbiterra       (),
    .sbiterra       (),
    .sleep          (1'b0),
    .regcea         (1'b1),
    // system bus
    .clka   (bus_mem[0].clk),
    .rsta   (bus_mem[0].rst),
    .ena    (bus_mem[0].vld),
    .wea    (bus_mem[0].ben & {DBW{bus_mem[0].wen}}),
    .addra  (bus_mem[0].adr[RAW-1:$clog2(DBW)]),
    .dina   (bus_mem[0].wdt),
    .douta  (bus_mem[0].rdt)
  );

  assign bus_mem[0].rdy = 1'b1;

end: gen_artix_xpm
else if (CHIP == "ARTIX_GEN") begin: gen_artix_gen

  blk_mem_gen_0 imem (
    .clka   (   bus_if.clk),
    .ena    (   bus_if.vld),
    .wea    ({4{bus_if.wen}}),
    .addra  (   bus_if.adr[IAW-1:2]),
    .dina   (   bus_if.wdt),
    .douta  (   bus_if.rdt)
  );

  assign bus_if.rdy = 1'b1;

  blk_mem_gen_0 dmem (
    .clka   (bus_mem[0].clk),
    .ena    (bus_mem[0].vld),
    .wea    (bus_mem[0].ben & {DBW{bus_mem[0].wen}}),
    .addra  (bus_mem[0].adr[RAW-1:$clog2(DBW)]),
    .dina   (bus_mem[0].wdt),
    .douta  (bus_mem[0].rdt)
  );

  assign bus_mem[0].rdy = 1'b1;

end: gen_artix_gen
else if (CHIP == "CYCLONE_V") begin: gen_cyclone_v

  rom32x4096 imem (
    // write access
    .clock      (bus_if.clk),
    .wren       (1'b0),
    .wraddress  ('x),
    .data       ('x),
    // read access
    .rdaddress  (bus_if.adr[IAW-1:2]),
    .rden       (bus_if.vld),
    .q          (bus_if.rdt)
  );

  assign bus_if.rdy = 1'b1;

  ram32x4096 dmem (
    .clock    (bus_mem[0].clk),
    .wren     (bus_mem[0].vld &  bus_mem[0].wen),
    .rden     (bus_mem[0].vld & ~bus_mem[0].wen),
    .address  (bus_mem[0].adr[RAW-1:$clog2(DBW)]),
    .byteena  (bus_mem[0].ben),
    .data     (bus_mem[0].wdt),
    .q        (bus_mem[0].rdt)
  );

  assign bus_mem[0].rdy = 1'b1;

end: gen_cyclone_v
else if (CHIP == "ECP5") begin: gen_ecp5

  // file:///usr/local/diamond/3.12/docs/webhelp/eng/index.htm#page/Reference%20Guides/IPexpress%20Modules/pmi_ram_dp.htm#
  pmi_ram_dp #(
    .pmi_wr_addr_depth     (8 * 2**RAW),
    .pmi_wr_addr_width     (RAW-$clog2(DBW)),
    .pmi_wr_data_width     (32),
    .pmi_rd_addr_depth     (8 * 2**RAW),
    .pmi_rd_addr_width     (RAW-$clog2(DBW)),
    .pmi_rd_data_width     (32),
    .pmi_regmode           ("reg"),
    .pmi_gsr               ("disable"),
    .pmi_resetmode         ("sync"),
    .pmi_optimization      ("speed"),
    .pmi_init_file         ("imem.mem"),
    .pmi_init_file_format  ("binary"),
    .pmi_family            ("ECP5")
  ) imem (
    // write access
    .WrClock    (bus_if.clk),
    .WrClockEn  (1'b0),
    .WE         (1'b0),
    .WrAddress  ('x),
    .Data       ('x),
    // read access
    .RdClock    (bus_if.clk),
    .RdClockEn  (1'b1),
    .Reset      (bus_mem[0].rst),
    .RdAddress  (bus_if.adr[IAW-1:2]),
    .Q          (bus_if.rdt)
  );

  assign bus_if.rdy = 1'b1;

  // TODO: use a single port or a true dual port memory
  pmi_ram_dp_be #(
    .pmi_wr_addr_depth     (8 * 2**RAW),
    .pmi_wr_addr_width     (RAW-$clog2(DBW)),
    .pmi_wr_data_width     (32),
    .pmi_rd_addr_depth     (8 * 2**RAW),
    .pmi_rd_addr_width     (RAW-$clog2(DBW)),
    .pmi_rd_data_width     (32),
    .pmi_regmode           ("reg"),
    .pmi_gsr               ("disable"),
    .pmi_resetmode         ("sync"),
    .pmi_optimization      ("speed"),
    .pmi_init_file         ("none"),
    .pmi_init_file_format  ("binary"),
    .pmi_byte_size         (8),
    .pmi_family            ("ECP5")
  ) dmem (
    .WrClock    (bus_mem[0].clk),
    .WrClockEn  (bus_mem[0].vld),
    .WE         (bus_mem[0].wen),
    .WrAddress  (bus_mem[0].adr[RAW-1:$clog2(DBW)]),
    .ByteEn     (bus_mem[0].ben),
    .Data       (bus_mem[0].wdt),
    .RdClock    (bus_mem[0].clk),
    .RdClockEn  (bus_mem[0].vld),
    .Reset      (bus_mem[0].rst),
    .RdAddress  (bus_mem[0].adr[RAW-1:$clog2(DBW)]),
    .Q          (bus_mem[0].rdt)
  );
 
  assign bus_mem[0].rdy = 1'b1;

end: gen_ecp5
else begin: gen_default

  // instruction memory
  r5p_soc_mem #(
    .FN   (IFN),
    .AW   (IAW),
    .DW   (IDW)
  ) imem (
    .bus  (bus_if)
  );

  // data memory
  r5p_soc_mem #(
  //.FN   (),
    .AW   (RAW-1),
    .DW   (DDW)
  ) dmem (
    .bus  (bus_mem[0])
  );

end: gen_default
endgenerate

////////////////////////////////////////////////////////////////////////////////
// GPIO
////////////////////////////////////////////////////////////////////////////////

// GPIO controller
r5p_soc_gpio #(
  .GW      (GW),
  .CFG_MIN (1'b1),
  .CHIP    (CHIP)
) soc_gpio (
  // GPIO signals
  .gpio_o  (gpio_o),
  .gpio_e  (gpio_e),
  .gpio_i  (gpio_i),
  // bus interface
  .bus     (bus_mem[1])
);

////////////////////////////////////////////////////////////////////////////////
// UART
////////////////////////////////////////////////////////////////////////////////

// TODO

endmodule: r5p_soc_top