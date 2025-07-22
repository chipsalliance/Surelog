/*****************************************************************************
 * Function: Dual Clock Asynchronous FIFO
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

module la_asyncfifo #(
    parameter DW    = 32,        // Memory width
    parameter DEPTH = 4,         // FIFO depth
    parameter NS    = 1,         // Number of power supplies
    parameter CTRLW = 1,         // width of asic ctrl interface
    parameter TESTW = 1,         // width of asic teset interface
    parameter CHAOS = 0,         // generates random full logic when set
    parameter TYPE  = "DEFAULT"  // Pass through variable for hard macro
) (  // write port
    input                  wr_clk,
    input                  wr_nreset,
    input      [   DW-1:0] wr_din,        // data to write
    input                  wr_en,         // write fifo
    input                  wr_chaosmode,  // randomly assert fifo full when set
    output reg             wr_full,       // fifo full
    // read port
    input                  rd_clk,
    input                  rd_nreset,
    output     [   DW-1:0] rd_dout,       // output data (next cycle)
    input                  rd_en,         // read fifo
    output reg             rd_empty,      // fifo is empty
    // Power signals
    input                  vss,           // ground signal
    input      [   NS-1:0] vdd,           // supplies
    // Generic interfaces
    input      [CTRLW-1:0] ctrl,          // pass through ASIC control interface
    input      [TESTW-1:0] test           // pass through ASIC test interface
);

    // local params
    // The last part is to support DEPTH of 1
    localparam AW = $clog2(DEPTH) + {31'h0, (DEPTH == 1)};

    // local wires
    reg  [AW:0] wr_grayptr;
    reg  [AW:0] wr_binptr;
    reg  [AW:0] wr_binptr_mem;
    wire [AW:0] wr_grayptr_nxt;
    wire [AW:0] wr_binptr_nxt;
    wire [AW:0] wr_binptr_mem_nxt;
    wire [AW:0] wr_grayptr_sync;
    wire        wr_chaosfull;

    reg  [AW:0] rd_grayptr;
    reg  [AW:0] rd_binptr;
    reg  [AW:0] rd_binptr_mem;
    wire [AW:0] rd_grayptr_nxt;
    wire [AW:0] rd_binptr_nxt;
    wire [AW:0] rd_binptr_mem_nxt;
    wire [AW:0] rd_grayptr_sync;

    genvar i;

    //###########################
    //# WRITE SIDE LOGIC
    //###########################

    always @(posedge wr_clk or negedge wr_nreset)
        if (~wr_nreset) begin
            wr_binptr_mem[AW:0] <= 'b0;
            wr_binptr[AW:0]     <= 'b0;
            wr_grayptr[AW:0]    <= 'b0;
        end else begin
            wr_binptr_mem[AW:0] <= (wr_binptr_mem_nxt[AW:0] == DEPTH) ? 'b0 : wr_binptr_mem_nxt[AW:0];
            wr_binptr[AW:0] <= wr_binptr_nxt[AW:0];
            wr_grayptr[AW:0] <= wr_grayptr_nxt[AW:0];
        end

    // Update binary pointer on write and not full
    assign wr_binptr_mem_nxt[AW:0] = wr_binptr_mem[AW-1:0] + {{(AW-1){1'b0}}, (wr_en && ~wr_full)};
    assign wr_binptr_nxt[AW:0] = wr_binptr[AW:0] + {{AW{1'b0}}, (wr_en && ~wr_full)};

    // Convert binary point to gray pointer for sync
    assign wr_grayptr_nxt[AW:0] = wr_binptr_nxt[AW:0] ^ {1'b0, wr_binptr_nxt[AW:1]};

    // Full comparison (gray pointer based)
    // Amir - add support for fifo DEPTH that is not power of 2
    // Note - the previous logic also had a bug that full was high one entry to soon

    reg [AW:0] rd_binptr_sync;
    wire [AW:0] fifo_used;
    integer j;

    always @(*) begin
        rd_binptr_sync[AW] = rd_grayptr_sync[AW];
        for (j = AW; j > 0; j = j - 1)
        rd_binptr_sync[j-1] = rd_binptr_sync[j] ^ rd_grayptr_sync[j-1];
    end

    assign fifo_used = wr_binptr - rd_binptr_sync;

    always @(posedge wr_clk or negedge wr_nreset)
        if (~wr_nreset) wr_full <= 1'b0;
        else
            wr_full <= (wr_chaosfull & wr_chaosmode) |
                  (fifo_used + {{AW{1'b0}}, (wr_en && ~wr_full)}) == DEPTH;

    // Write --> Read clock synchronizer
    for (i = 0; i < (AW + 1); i = i + 1) begin
        la_drsync wrsync (
            .out(wr_grayptr_sync[i]),
            .clk(rd_clk),
            .nreset(rd_nreset),
            .in(wr_grayptr[i])
        );
    end

    //###########################
    //# READ SIDE LOGIC
    //###########################

    always @(posedge rd_clk or negedge rd_nreset)
        if (~rd_nreset) begin
            rd_binptr_mem[AW:0] <= 'b0;
            rd_binptr[AW:0]     <= 'b0;
            rd_grayptr[AW:0]    <= 'b0;
        end else begin
            rd_binptr_mem[AW:0] <= (rd_binptr_mem_nxt[AW:0] == DEPTH) ? 'b0 : rd_binptr_mem_nxt[AW:0];
            rd_binptr[AW:0] <= rd_binptr_nxt[AW:0];
            rd_grayptr[AW:0] <= rd_grayptr_nxt[AW:0];
        end

    assign rd_binptr_mem_nxt[AW:0] = rd_binptr_mem[AW-1:0] + {{(AW-1){1'b0}}, (rd_en && ~rd_empty)};
    assign rd_binptr_nxt[AW:0] = rd_binptr[AW:0] + {{AW{1'b0}}, (rd_en && ~rd_empty)};
    assign rd_grayptr_nxt[AW:0] = rd_binptr_nxt[AW:0] ^ {1'b0, rd_binptr_nxt[AW:1]};

    // Full comparison (gray pointer based)
    always @(posedge rd_clk or negedge rd_nreset)
        if (~rd_nreset) rd_empty <= 1'b1;
        else rd_empty <= (rd_grayptr_nxt[AW:0] == wr_grayptr_sync[AW:0]);

    // Read --> write clock synchronizer
    for (i = 0; i < (AW + 1); i = i + 1) begin
        la_drsync rdsync (
            .out(rd_grayptr_sync[i]),
            .clk(wr_clk),
            .nreset(wr_nreset),
            .in(rd_grayptr[i])
        );
    end

    //###########################
    //# Dual Port Memory
    //###########################

    reg [DW-1:0] ram[DEPTH-1:0];

    // Write port (FIFO input)
    always @(posedge wr_clk) if (wr_en & ~wr_full) ram[wr_binptr_mem[AW-1:0]] <= wr_din[DW-1:0];

    // Read port (FIFO output)
    assign rd_dout[DW-1:0] = ram[rd_binptr_mem[AW-1:0]];

    //############################
    // Randomly Asserts FIFO full
    //############################

    generate
        if (CHAOS) begin
            // TODO: implement LFSR
            reg chaosreg;
            always @(posedge wr_clk or negedge wr_nreset)
                if (~wr_nreset) chaosreg <= 1'b0;
                else chaosreg <= ~chaosreg;
            assign wr_chaosfull = chaosreg;
        end else begin
            assign wr_chaosfull = 1'b0;
        end

    endgenerate


endmodule
