/*****************************************************************************
 * Function: Single Port ram
 * Copyright: Lambda Project Authors. All rights Reserved.
 * License:  MIT (see LICENSE file in Lambda repository)
 *
 * Docs:
 *
 * This is a wrapper for selecting from a set of hardened memory macros.
 *
 * A synthesizable reference model is used when the TYPE is DEFAULT. The
 * synthesizable model does not implement the cfg and test interface and should
 * only be used for basic testing and for synthesizing for FPGA devices.
 * Advanced ASIC development should rely on complete functional models
 * supplied on a per macro basis.
 *
 * Technologoy specific implementations of "la_spram" would generally include
 * one ore more hardcoded instantiations of ram modules with a generate
 * statement relying on the "TYPE" to select between the list of modules
 * at build time.
 *
 ****************************************************************************/

module la_spram
  #(parameter DW     = 32,          // Memory width
    parameter AW     = 10,          // Address width (derived)
    parameter TYPE   = "DEFAULT",   // Pass through variable for hard macro
    parameter CTRLW  = 128,         // Width of asic ctrl interface
    parameter TESTW  = 128          // Width of asic test interface
    )
   (// Memory interface
    input clk, // write clock
    input ce, // chip enable
    input we, // write enable
    input [DW-1:0] wmask, //per bit write mask
    input [AW-1:0] addr, //write address
    input [DW-1:0] din, //write data
    output [DW-1:0] dout, //read output data
    // Power signals
    input vss, // ground signal
    input vdd, // memory core array power
    input vddio, // periphery/io power
    // Generic interfaces
    input [CTRLW-1:0] ctrl, // pass through ASIC control interface
    input [TESTW-1:0] test // pass through ASIC test interface
    );

    // Determine which memory to select
    localparam MEM_TYPE = (TYPE != "DEFAULT") ? TYPE :
      (AW >= 9) ? (DW >= 64) ? "fakeram45_512x64" : "fakeram45_512x32" :
      (AW == 8) ? (DW >= 64) ? "fakeram45_256x64" : "fakeram45_256x32" :
      (AW == 7) ? "fakeram45_128x32" :
      "fakeram45_64x32";

    localparam MEM_WIDTH = 
      (MEM_TYPE == "fakeram45_128x32") ? 32 :
      (MEM_TYPE == "fakeram45_256x32") ? 32 :
      (MEM_TYPE == "fakeram45_256x64") ? 64 :
      (MEM_TYPE == "fakeram45_512x32") ? 32 :
      (MEM_TYPE == "fakeram45_512x64") ? 64 :
      (MEM_TYPE == "fakeram45_64x32") ? 32 :
      0;
 
    localparam MEM_DEPTH = 
      (MEM_TYPE == "fakeram45_128x32") ? 7 :
      (MEM_TYPE == "fakeram45_256x32") ? 8 :
      (MEM_TYPE == "fakeram45_256x64") ? 8 :
      (MEM_TYPE == "fakeram45_512x32") ? 9 :
      (MEM_TYPE == "fakeram45_512x64") ? 9 :
      (MEM_TYPE == "fakeram45_64x32") ? 6 :
      0;

    // Create memories
    localparam MEM_ADDRS = 2**(AW - MEM_DEPTH) < 1 ? 1 : 2**(AW - MEM_DEPTH);

    

    generate
      genvar o;
      for (o = 0; o < DW; o = o + 1) begin: OUTPUTS
        wire [MEM_ADDRS-1:0] mem_outputs;
        assign dout[o] = |mem_outputs;
      end

      genvar a;
      for (a = 0; a < MEM_ADDRS; a = a + 1) begin: ADDR
        wire selected;
        wire [MEM_DEPTH-1:0] mem_addr;

        if (MEM_ADDRS == 1) begin: FITS
          assign selected = 1'b1;
          assign mem_addr = addr;
        end else begin: NOFITS
          assign selected = addr[AW-1:MEM_DEPTH] == a;
          assign mem_addr = addr[MEM_DEPTH-1:0];
        end

        genvar n;
        for (n = 0; n < DW; n = n + MEM_WIDTH) begin: WORD
          wire [MEM_WIDTH-1:0] mem_din;
          wire [MEM_WIDTH-1:0] mem_dout;
          wire [MEM_WIDTH-1:0] mem_wmask;

          genvar i;
          for (i = 0; i < MEM_WIDTH; i = i + 1) begin: WORD_SELECT
            if (n + i < DW) begin: ACTIVE
              assign mem_din[i] = din[n + i];
              assign mem_wmask[i] = wmask[n + i];
              assign OUTPUTS[n + i].mem_outputs[a] = selected ? mem_dout[i] : 1'b0;
            end
            else begin: INACTIVE
              assign mem_din[i] = 1'b0;
              assign mem_wmask[i] = 1'b0;
            end
          end

          wire ce_in;
          wire we_in;
          assign ce_in = ce && selected;
          assign we_in = we && selected;
          
          if (MEM_TYPE == "fakeram45_512x32")
            fakeram45_512x32 memory (
              .addr_in(mem_addr),
              .ce_in(ce_in),
              .clk(clk),
              .rd_out(mem_dout),
              .w_mask_in(mem_wmask),
              .wd_in(mem_din),
              .we_in(we_in)
            );
          else if (MEM_TYPE == "fakeram45_512x64")
            fakeram45_512x64 memory (
              .addr_in(mem_addr),
              .ce_in(ce_in),
              .clk(clk),
              .rd_out(mem_dout),
              .w_mask_in(mem_wmask),
              .wd_in(mem_din),
              .we_in(we_in)
            );
          else if (MEM_TYPE == "fakeram45_256x64")
            fakeram45_256x64 memory (
              .addr_in(mem_addr),
              .ce_in(ce_in),
              .clk(clk),
              .rd_out(mem_dout),
              .w_mask_in(mem_wmask),
              .wd_in(mem_din),
              .we_in(we_in)
            );
          else if (MEM_TYPE == "fakeram45_256x32")
            fakeram45_256x32 memory (
              .addr_in(mem_addr),
              .ce_in(ce_in),
              .clk(clk),
              .rd_out(mem_dout),
              .w_mask_in(mem_wmask),
              .wd_in(mem_din),
              .we_in(we_in)
            );
          else if (MEM_TYPE == "fakeram45_128x32")
            fakeram45_128x32 memory (
              .addr_in(mem_addr),
              .ce_in(ce_in),
              .clk(clk),
              .rd_out(mem_dout),
              .w_mask_in(mem_wmask),
              .wd_in(mem_din),
              .we_in(we_in)
            );
          else if (MEM_TYPE == "fakeram45_64x32")
            fakeram45_64x32 memory (
              .addr_in(mem_addr),
              .ce_in(ce_in),
              .clk(clk),
              .rd_out(mem_dout),
              .w_mask_in(mem_wmask),
              .wd_in(mem_din),
              .we_in(we_in)
            );
        end
      end
    endgenerate
endmodule