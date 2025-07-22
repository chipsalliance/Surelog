/*****************************************************************************
 * Function: Dual Port RAM (One write port + One read port)
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
 * Technologoy specific implementations of "la_dpram" would generally include
 * one ore more hardcoded instantiations of RAM modules with a generate
 * statement relying on the "TYPE" to select between the list of modules
 * at build time.
 *
 ****************************************************************************/

module la_dpram #(
    parameter DW    = 32,         // Memory width
    parameter AW    = 10,         // address width (derived)
    parameter TYPE  = "DEFAULT",  // pass through variable for hard macro
    parameter CTRLW = 128,        // width of asic ctrl interface
    parameter TESTW = 128         // width of asic test interface
) (  // Write port
    input wr_clk,  // write clock
    input wr_ce,  // write chip-enable
    input wr_we,  // write enable
    input [DW-1:0] wr_wmask,  // write mask
    input [AW-1:0] wr_addr,  // write address
    input [DW-1:0] wr_din,  //write data in
    // Read port
    input rd_clk,  // read clock
    input rd_ce,  // read chip-enable
    input [AW-1:0] rd_addr,  // read address
    output reg [DW-1:0] rd_dout,  //read data out
    // Power signal
    input vss,  // ground signal
    input vdd,  // memory core array power
    input vddio,  // periphery/io power
    // Generic interfaces
    input [CTRLW-1:0] ctrl,  // pass through ASIC control interface
    input [TESTW-1:0] test  // pass through ASIC test interface
);

    // Generic RTL RAM
    reg     [DW-1:0] ram[(2**AW)-1:0];
    integer          i;

    // Write port
    always @(posedge wr_clk)
        for (i = 0; i < DW; i = i + 1)
            if (wr_ce & wr_we & wr_wmask[i]) ram[wr_addr[AW-1:0]][i] <= wr_din[i];

    // Read Port
    always @(posedge rd_clk) if (rd_ce) rd_dout[DW-1:0] <= ram[rd_addr[AW-1:0]];

endmodule
