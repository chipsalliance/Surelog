
/*********************************************************************************
Copyright (c) 2021 Wavious LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

*********************************************************************************/

module wav_tcm_sp #(
   parameter       AWIDTH      = 32,
   parameter       DWIDTH      = 32,       // SRAM Width in Bits
   parameter       DEPTH       = 2048,     // Maximum SRAM WORDS
   parameter       STRB_WIDTH  = (DWIDTH/8),
   parameter       SIZE        = 65536,    // TCM Size in KB
   parameter       PIPELINE    = 0,
   parameter  CDE_FILE_INIT    = "default.hex",
   parameter INITIAL_MEM_DELAY = 450
)(
   input  logic                  i_clk,
   input  logic                  i_reset,
   input  logic                  i_cs,       // Chip select/RAM enable
   input  logic     [AWIDTH-1:0] i_addr,     // Address
   input  logic                  i_wr,       // Write/not read
   input  logic [STRB_WIDTH-1:0] i_byte_wr,  // Byte strobes
   input  logic     [DWIDTH-1:0] i_wdata,    // Write data
   input  logic                  i_sleep,
   input  logic            [7:0] i_tcm_cfg,

   output logic     [DWIDTH-1:0] o_rdata,    // Read data
   output logic                  o_wait,
   output logic                  o_error
);

   localparam MAX_SRAM_WIDTH     = 64;
   localparam MAX_SRAM_DEPTH     = 2048;
   localparam REAL_SRAM_WIDTH    = (DWIDTH > MAX_SRAM_WIDTH) ? MAX_SRAM_WIDTH : DWIDTH;
   localparam REAL_SRAM_DEPTH    = (DEPTH > MAX_SRAM_DEPTH) ? MAX_SRAM_DEPTH : DEPTH;
   localparam NUM_SRAM_BYTE      = REAL_SRAM_DEPTH * (REAL_SRAM_WIDTH/8);

   localparam NUM_BYTE           = REAL_SRAM_DEPTH * (DWIDTH/8);
   localparam NUM_SRAM           = (NUM_BYTE > SIZE) ? 1 : SIZE/NUM_BYTE;
   localparam LSB_ADR            = $clog2(NUM_BYTE);
   localparam MSB_ADR            = (NUM_BYTE >= SIZE) ? LSB_ADR + 1 : $clog2(SIZE);
   localparam WORD_ADR           = $clog2(DWIDTH/8);

   wire    [DWIDTH-1:0] rd_sram [NUM_SRAM-1:0];
   logic   [DWIDTH-1:0] rdata_q ;
   wire    [DWIDTH-1:0] rdata_out ;
   logic                wait_out ;
   logic                wait_q ;
   logic                wr_q ;
   logic                cs_q ;

   logic                  web;
   logic [DWIDTH-1:0]     bweb;
   logic [NUM_SRAM-1:0]   ceb;

   logic                  we;
   logic [DWIDTH-1:0]     bwe;
   logic [NUM_SRAM-1:0]   ce;

   logic                  cs_dly;
   logic [AWIDTH-1:0]     addr_dly;
   logic [AWIDTH-1:0]     addr_q;
   logic                  wr_dly;
   logic [STRB_WIDTH-1:0] byte_wr_dly;
   logic [DWIDTH-1:0]     wdata_dly;

   assign cs_dly      = i_cs;
   assign addr_dly    = i_addr;
   assign wr_dly      = i_wr;
   assign byte_wr_dly = i_byte_wr;
   assign wdata_dly   = i_wdata;

   assign o_error = 1'b0;

   logic [STRB_WIDTH-1:0] byte_wr_int;
   assign byte_wr_int = byte_wr_dly << addr_dly[WORD_ADR-1:0] ;

   logic msbAddress;
   assign msbAddress = |addr_dly[AWIDTH-1:MSB_ADR];

   assign web = ~wr_dly;
   assign we  =  wr_dly;

   int j;
   always_comb begin
      for (j=0; j<DWIDTH/8; j++)
           bweb[j*8 +:8] = {8{~byte_wr_int[j]}};
      for (j=0; j<DWIDTH/8; j++)
           bwe [j*8 +:8] = {8{ byte_wr_int[j]}};
   end

   generate
      if (PIPELINE) begin : pipeline
         always_ff @(posedge i_clk or posedge i_reset ) begin
            if (i_reset) begin
               rdata_q <= 'b0;
               wait_q  <= 'b1;
            end
            else begin
               wait_q <= ~o_wait & cs_dly;
               if (o_wait)
                  rdata_q <= rd_sram[addr_dly[MSB_ADR-1:LSB_ADR]];
            end
         end
      end else begin
         assign rdata_q = '0;
         assign wait_q = '0;
      end
   endgenerate

   always_ff @(posedge i_clk or posedge i_reset ) begin
      if (i_reset) begin
         addr_q <= 'b0;
      end
      else if ( addr_q != addr_dly ) begin
         addr_q <= addr_dly ;
      end
   end

   always_ff @(posedge i_clk or posedge i_reset ) begin
      if (i_reset) begin
         cs_q     <= 'b0;
         wr_q     <= 'b0;
      end
      else if ( cs_dly || cs_q ) begin
         cs_q     <= cs_dly ;
         wr_q     <= wr_dly ;
      end
   end

   assign wait_out =  ~(cs_dly & wr_dly) & (~cs_q | (cs_q & wr_q)) ;

   assign rdata_out =  rd_sram[addr_q[MSB_ADR-1:LSB_ADR]];
   assign o_rdata = (PIPELINE == 0) ? rdata_out : rdata_q;
   assign o_wait  = (PIPELINE == 0) ? wait_out  : wait_q;

   genvar i, k;
   generate
      for (i=0; i<NUM_SRAM; i++) begin : tcm_sram

         assign ceb[i] = (~(cs_dly&(addr_dly[MSB_ADR-1:LSB_ADR] == i)&(~msbAddress)) |   i_sleep);
         assign ce[i]  = ( (cs_dly&(addr_dly[MSB_ADR-1:LSB_ADR] == i)&(~msbAddress)) &  ~i_sleep);

         if (DWIDTH >= 64) begin : tcm_wide
            for (k=0; k<DWIDTH/MAX_SRAM_WIDTH; k++) begin : parallel_ram
            `ifndef WAV_FPGA
              `ifdef WAV_RAM_GF12LPP
                 S10S2048x64M44 tcm_sram (
                  .CLK      (i_clk),
                  .CEN      (ceb[i]),
                  .GWEN     (web),
                  .A        (addr_dly[LSB_ADR-1:WORD_ADR]),
                  .D        (wdata_dly[k*64+:64]),
                  .Q        (rd_sram[i][k*64+:64]),
                  .WEN      (bweb[k*64+:64]),
                  .STOV     (i_tcm_cfg[6]),
                  .EMA      (i_tcm_cfg[2:0]),
                  .EMAW     (i_tcm_cfg[4:3]),
                  .EMAS     (i_tcm_cfg[5]),
                  .RET1N    (1'b1)
                 );
              `elsif WAV_RAM_TSMC12FFC
                 `ifndef SYNTHESIS
                  TS1N12FFCLLSBSVTD2048X64M8SWS #(
                     .INITIAL_MEM_DELAY (INITIAL_MEM_DELAY)
                  ) tcm_sram (
                 `else
                  TS1N12FFCLLSBSVTD2048X64M8SWS tcm_sram (
                 `endif
                   .CLK      (i_clk),
                   .A        (addr_dly[LSB_ADR-1:WORD_ADR]),
                   .SLP      (i_sleep),
                   .D        (wdata_dly[k*64+:64]),
                   .Q        (rd_sram[i][k*64+:64]),
                   .WEB      (web),
                   .CEB      (ceb[i]),
                   .BWEB     (bweb[k*64+:64]),
                   .RTSEL    (2'b01),
                   .WTSEL    (2'b00)
                  );
              `else // Behavioral
                  wav_ram_sp #(
                     .DWIDTH   (32),
                     .SIZE     (2048),
                     .PIPELINE (1)
                  ) tcm_sram (
                     .i_clk  (i_clk),
                     .i_addr (addr_dly[LSB_ADR-1:WORD_ADR]),
                     .i_en   (ce[i]),
                     .i_we   (we),
                     .i_be   (byte_wr_int[k*8+:8]),
                     .i_wdata(wdata_dly[k*64+:64]),
                     .o_rdata(rd_sram[i][k*64+:64])
                  );
              `endif
            `else // WAV_FPGA
               blk_mem_gen_2048X64_sp tcm_sram (
                  .clka   (i_clk),                        // input  wire        clka
                  .ena    (ce[i]),                        // input  wire        ena
                  .wea    (bwe[k*8+:8]),                  // input  wire [7:0 ] wea
                  .addra  (addr_dly[LSB_ADR-1:WORD_ADR]), // input  wire [10:0] addra
                  .dina   (wdata_dly[k*64+:64]),          // input  wire [63:0] datain
                  .douta  (rd_sram[i][k*64+:64])          // output wire [63:0] douta
               );
            `endif
            end
         end else if (DWIDTH == 64) begin : tcm_64bit
         `ifndef WAV_FPGA
           `ifdef WAV_RAM_GF12LPP
              S10S2048x64M44 tcm_sram (
               .CLK      (i_clk),
               .CEN      (ceb[i]),
               .GWEN     (web),
               .A        (addr_dly[LSB_ADR-1:WORD_ADR]),
               .D        (wdata_dly),
               .Q        (rd_sram[i]),
               .WEN      (bweb),
               .STOV     (i_tcm_cfg[6]),
               .EMA      (i_tcm_cfg[2:0]),
               .EMAW     (i_tcm_cfg[4:3]),
               .EMAS     (i_tcm_cfg[5]),
               .RET1N    (1'b1)
            );
           `elsif WAV_RAM_TSMC12FFC
              `ifndef SYNTHESIS
               TS1N12FFCLLSBSVTD2048X64M8SWS #(
                  .INITIAL_MEM_DELAY (INITIAL_MEM_DELAY)
               ) tcm_sram (
              `else
               TS1N12FFCLLSBSVTD2048X64M8SWS tcm_sram (
              `endif
                .CLK      (i_clk),
                .A        (addr_dly[LSB_ADR-1:WORD_ADR]),
                .SLP      (i_sleep),
                .D        (wdata_dly),
                .Q        (rd_sram[i]),
                .WEB      (web),
                .CEB      (ceb[i]),
                .BWEB     (bweb),
                .RTSEL    (2'b01),
                .WTSEL    (2'b00)
               );
           `else // Behavioral
               wav_ram_sp #(
                  .DWIDTH   (32),
                  .SIZE     (2048),
                  .PIPELINE (1)
               ) tcm_sram (
                  .i_clk  (i_clk),
                  .i_addr (addr_dly[LSB_ADR-1:WORD_ADR]),
                  .i_en   (ce[i]),
                  .i_we   (we),
                  .i_be   (byte_wr_int),
                  .i_wdata(wdata_dly),
                  .o_rdata(rd_sram[i])
               );
           `endif
         `else // WAV_FPGA
              blk_mem_gen_2048X64_sp tcm_sram (
                 .clka   (i_clk),                        // input  wire        clka
                 .ena    (ce[i]),                        // input  wire        ena
                 .wea    (byte_wr_int),                  // input  wire [7:0 ] wea
                 .addra  (addr_dly[LSB_ADR-1:WORD_ADR]), // input  wire [10:0] addra
                 .dina   (wdata_dly),                    // input  wire [63:0] datain
                 .douta  (rd_sram[i])                    // output wire [63:0] douta
              );
         `endif
         end else begin : tcm_32bit
         `ifndef WAV_FPGA
           `ifdef WAV_RAM_GF12LPP
              S10S2048x32M44 tcm_sram (
               .CLK      (i_clk),
               .CEN      (ceb[i]),
               .GWEN     (web),
               .A        (addr_dly[LSB_ADR-1:WORD_ADR]),
               .D        (wdata_dly),
               .Q        (rd_sram[i]),
               .WEN      (bweb),
               .STOV     (i_tcm_cfg[6]),
               .EMA      (i_tcm_cfg[2:0]),
               .EMAW     (i_tcm_cfg[4:3]),
               .EMAS     (i_tcm_cfg[5]),
               .RET1N    (1'b1)
              );
           `elsif WAV_RAM_TSMC12FFC
              `ifndef SYNTHESIS
               TS1N12FFCLLSBSVTD2048X32M8SWS #(
                  .INITIAL_MEM_DELAY (INITIAL_MEM_DELAY)
               )  tcm_sram (
              `else
               TS1N12FFCLLSBSVTD2048X32M8SWS tcm_sram (
              `endif
                .CLK      (i_clk),
                .A        (addr_dly[LSB_ADR-1:WORD_ADR]),
                .SLP      (i_sleep),
                .D        (wdata_dly),
                .Q        (rd_sram[i]),
                .WEB      (web),
                .CEB      (ceb[i]),
                .BWEB     (bweb),
                .RTSEL    (2'b01),
                .WTSEL    (2'b00)
               );
           `else // Behavioral
               wav_ram_sp #(
                  .DWIDTH   (32),
                  .SIZE     (2048),
                  .PIPELINE (1)
               ) tcm_sram (
                  .i_clk  (i_clk),
                  .i_addr (addr_dly[LSB_ADR-1:WORD_ADR]),
                  .i_en   (ce[i]),
                  .i_we   (we),
                  .i_be   (byte_wr_int),
                  .i_wdata(wdata_dly),
                  .o_rdata(rd_sram[i])
               );
           `endif
         `else // WAV_FPGA
              blk_mem_gen_2048X32_sp tcm_sram (
                 .clka   (i_clk),                        // input  wire        clka
                 .ena    (ce[i]),                        // input  wire        ena
                 .wea    (byte_wr_int),                  // input  wire [7:0 ] wea
                 .addra  (addr_dly[LSB_ADR-1:WORD_ADR]), // input  wire [10:0] addra
                 .dina   (wdata_dly),                    // input  wire [63:0] datain
                 .douta  (rd_sram[i])                    // output wire [63:0] douta
              );
         `endif
         end
      end
   endgenerate

   task automatic print_stats;
      $display("Target SRAM Size (Bytes)\t= %d", SIZE);
      $display("Unit SRAM Size (Bytes)\t\t= %d", NUM_SRAM_BYTE);
      $display("Number of SRAMs Required\t= %d", (NUM_SRAM * ((DWIDTH/MAX_SRAM_WIDTH) ? DWIDTH/MAX_SRAM_WIDTH : 1)));
      $display("SRAM LSb\t\t\t= %d", LSB_ADR);
      $display("SRAM MSb\t\t\t= %d", MSB_ADR);
      $display("SRAM WORD Offset\t\t= %d", WORD_ADR);
   endtask

`ifdef WAV_SRAM_SIZE_ASSERT_ON
   initial begin
      print_stats();
   end
`endif

endmodule
