/*
 * LatticeMico32
 * Instruction Translation Lookaside Buffer
 *
 * Copyright (c) 2011-2012 Yann Sionneau <yann.sionneau@gmail.com>
 * Copyright (c) 2012 Michael Walle <michael@walle.cc>
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. The name of the author may not be used to endorse or promote products
 *    derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 * IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 * NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

`include "lm32_include.v"

`ifdef CFG_MMU_ENABLED
`define LM32_ITLB_CTRL_FLUSH                5'h1
`define LM32_ITLB_CTRL_UPDATE               5'h2
`define LM32_TLB_CTRL_INVALIDATE_ENTRY      5'h10

`define LM32_ITLB_STATE_RNG               1:0
`define LM32_ITLB_STATE_CHECK             2'b01
`define LM32_ITLB_STATE_FLUSH             2'b10

`define LM32_ITLB_OFFSET_RNG  offset_msb:offset_lsb
`define LM32_ITLB_IDX_RNG     index_msb:index_lsb
`define LM32_ITLB_VPFN_RNG    vpfn_msb:vpfn_lsb
`define LM32_ITLB_TAG_RNG     tag_msb:tag_lsb
`define LM32_ITLB_ADDR_RNG    (index_width-1):0
`define LM32_ITLB_DATA_WIDTH  (vpfn_width+tag_width+1)
`define LM32_ITLB_DATA_RNG    (`LM32_ITLB_DATA_WIDTH-1):0


/////////////////////////////////////////////////////
// Module interface
/////////////////////////////////////////////////////
module lm32_itlb (
    // ----- Inputs -------
    clk_i,
    rst_i,
    enable,
    stall_a,
    stall_f,
    stall_d,
    stall_x,
    pc_a,
    pc_f,
    pc_x,
    read_enable_f,
    tlbpaddr,
    tlbvaddr,
    update,
    flush,
    invalidate,
    // ----- Outputs -------
    physical_pc_f,
    stall_request,
    miss_vfn,
    miss_f,
    miss_x
    );

/////////////////////////////////////////////////////
// Parameters
/////////////////////////////////////////////////////

parameter entries = 1024;               // Number of entires in ITLB
parameter page_size = 4096;             // ITLB page size

localparam offset_width = (`CLOG2(page_size)-2);
localparam index_width = `CLOG2(entries);
localparam offset_lsb = 2;
localparam offset_msb = (offset_lsb+offset_width-1);
localparam index_lsb = (offset_msb+1);
localparam index_msb = (index_lsb+index_width-1);
localparam tag_lsb = (index_msb+1);
localparam tag_msb = (`LM32_WORD_WIDTH-1);
localparam tag_width = (tag_msb-tag_lsb+1);
localparam vpfn_lsb = (offset_msb+1);
localparam vpfn_msb = (`LM32_WORD_WIDTH-1);
localparam vpfn_width = (vpfn_msb-vpfn_lsb+1);

/////////////////////////////////////////////////////
// Inputs
/////////////////////////////////////////////////////

input clk_i;                            // Clock
input rst_i;                            // Reset

input enable;                           // Instruction TLB enable
input stall_a;                          // Stall instruction in A stage
input stall_f;                          // Stall instruction in F stage
input stall_d;                          // Stall instruction in D stage
input stall_x;                          // Stall instruction in X stage

input [`LM32_PC_RNG] pc_a;              // Address of instruction in A stage
input [`LM32_PC_RNG] pc_f;              // Address of instruction in F stage
input [`LM32_PC_RNG] pc_x;              // Address of instruction in X stage

input read_enable_f;                    // Indicates if cache access is valid

input [`LM32_WORD_RNG] tlbpaddr;
input [`LM32_WORD_RNG] tlbvaddr;
input update;
input flush;
input invalidate;

/////////////////////////////////////////////////////
// Outputs
/////////////////////////////////////////////////////
output [`LM32_PC_RNG] physical_pc_f;
reg    [`LM32_PC_RNG] physical_pc_f;
output stall_request;
wire   stall_request;
output [`LM32_WORD_RNG] miss_vfn;
wire   [`LM32_WORD_RNG] miss_vfn;
output miss_f;
wire   miss_f;
output miss_x;
reg    miss_x;

/////////////////////////////////////////////////////
// Internal nets and registers
/////////////////////////////////////////////////////

wire [`LM32_ITLB_ADDR_RNG] read_address;
wire [`LM32_ITLB_ADDR_RNG] write_address;
wire read_port_enable;
wire write_port_enable;
wire [`LM32_ITLB_DATA_RNG] write_data;
reg [`LM32_ITLB_STATE_RNG] state;
reg [`LM32_ITLB_ADDR_RNG] flush_set;

wire [`LM32_ITLB_TAG_RNG] tlbe_tag_f;
wire [`LM32_ITLB_VPFN_RNG] tlbe_pfn_f;
wire tlbe_valid_f;

reg miss_d;

/////////////////////////////////////////////////////
// Functions
/////////////////////////////////////////////////////

////////////////////////////////////////////////////
// Instantiations
/////////////////////////////////////////////////////

lm32_ram
  #(
    // ----- Parameters -------
    .data_width (`LM32_ITLB_DATA_WIDTH),
    .address_width (index_width)
// Modified for Milkymist: removed non-portable RAM parameters
    ) data_ram
    (
     // ----- Inputs -------
     .read_clk (clk_i),
     .write_clk (clk_i),
     .reset (rst_i),
     .read_address (read_address),
     .enable_read (read_port_enable),
     .write_address (write_address),
     .enable_write (`TRUE),
     .write_enable (write_port_enable),
     .write_data (write_data),
     // ----- Outputs -------
     .read_data ({tlbe_pfn_f, tlbe_tag_f, tlbe_valid_f})
     );

/////////////////////////////////////////////////////
// Combinational logic
/////////////////////////////////////////////////////

// Compute address to use to index into the ITLB memory
assign read_address = pc_a[`LM32_ITLB_IDX_RNG];
assign write_address = (flushing == `TRUE) ? flush_set : tlbvaddr[`LM32_ITLB_IDX_RNG];

assign read_port_enable = (stall_a == `FALSE);
assign write_port_enable = (update == `TRUE) || (invalidate == `TRUE) || (flushing == `TRUE);

assign write_data = ((invalidate == `TRUE) || (flushing == `TRUE))
             ? {{`LM32_ITLB_DATA_WIDTH-1{1'b0}}, `FALSE}
             : {tlbpaddr[`LM32_ITLB_VPFN_RNG], tlbvaddr[`LM32_ITLB_TAG_RNG], `TRUE};

assign tlbe_match_f = ({tlbe_tag_f, tlbe_valid_f} == {pc_f[`LM32_ITLB_TAG_RNG], `TRUE});

assign miss_vfn = {pc_x[`LM32_ITLB_VPFN_RNG], {offset_width{1'b0}}, 2'b0};
assign miss_f = (enable == `TRUE) && (tlbe_match_f == `FALSE) && (stall_f == `FALSE);

assign flushing = state[1];
assign stall_request = (flushing == `TRUE);

always @(*)
begin
    if (enable == `TRUE)
    begin
        if (tlbe_match_f == `TRUE)
            physical_pc_f = {tlbe_pfn_f, pc_f[`LM32_ITLB_OFFSET_RNG]};
        else
            physical_pc_f = {`LM32_PC_WIDTH{1'b0}};
    end
    else
        physical_pc_f = pc_f;
end

/////////////////////////////////////////////////////
// Sequential logic
/////////////////////////////////////////////////////

always @(posedge clk_i `CFG_RESET_SENSITIVITY)
begin
    if (rst_i == `TRUE)
    begin
        miss_d <= `FALSE;
        miss_x <= `FALSE;
    end
    else
    begin
        if (stall_d == `FALSE)
            miss_d <= miss_f;
        if (stall_x == `FALSE)
            miss_x <= miss_d;
    end
end

always @(posedge clk_i `CFG_RESET_SENSITIVITY)
begin
    if (rst_i == `TRUE)
    begin
        flush_set <= {index_width{1'b1}};
        state <= `LM32_ITLB_STATE_FLUSH;
    end
    else
    begin
        case (state)

        `LM32_ITLB_STATE_CHECK:
        begin
            if (flush == `TRUE)
            begin
                flush_set <= {index_width{1'b1}};
                state <= `LM32_ITLB_STATE_FLUSH;
            end
        end

        `LM32_ITLB_STATE_FLUSH:
        begin
            if (flush_set == {index_width{1'b0}})
                state <= `LM32_ITLB_STATE_CHECK;
            flush_set <= flush_set - 1'b1;
        end

        endcase
    end
end

endmodule

`endif

