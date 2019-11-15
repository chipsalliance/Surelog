/*
 * LatticeMico32
 * True dual-ported RAM
 *
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

/////////////////////////////////////////////////////
// Module interface
/////////////////////////////////////////////////////

module lm32_dp_ram (
    // ----- Inputs -------
    clk_a,
    clk_b,
    ce_a,
    ce_b,
    addr_a,
    addr_b,
    di_a,
    di_b,
    we_a,
    we_b,
    // ----- Outputs -------
    do_a,
    do_b
    );

/////////////////////////////////////////////////////
// Parameters
/////////////////////////////////////////////////////

parameter data_width = 1;               // Width of the data ports
parameter address_width = 1;            // Width of the address ports
parameter init_file = "NONE";           // Initialization file

/////////////////////////////////////////////////////
// Inputs
/////////////////////////////////////////////////////

input clk_a;                            // Clock port A
input clk_b;                            // Clock port B

input ce_a;                             // Clock enable port A
input ce_b;                             // Clock enable port B
input [address_width-1:0] addr_a;       // Read/write address port A
input [address_width-1:0] addr_b;       // Read/write address port B
input [data_width-1:0] di_a;            // Data input port A
input [data_width-1:0] di_b;            // Data input port B
input we_a;                             // Write enable port A
input we_b;                             // Write enable port B

/////////////////////////////////////////////////////
// Outputs
/////////////////////////////////////////////////////

output [data_width-1:0] do_a;           // Data output port A
wire   [data_width-1:0] do_a;

output [data_width-1:0] do_b;           // Data output port B
wire   [data_width-1:0] do_b;

/////////////////////////////////////////////////////
// Internal nets and registers
/////////////////////////////////////////////////////

reg [data_width-1:0]    mem[0:(1<<address_width)-1];
reg [address_width-1:0] ra_a;           // Registered read address port A
reg [address_width-1:0] ra_b;           // Registered read address port B

/////////////////////////////////////////////////////
// Functions
/////////////////////////////////////////////////////

////////////////////////////////////////////////////
// Instantiations
/////////////////////////////////////////////////////

/////////////////////////////////////////////////////
// Combinational logic
/////////////////////////////////////////////////////

// Read ports
assign do_a = mem[ra_a];
assign do_b = mem[ra_b];

/////////////////////////////////////////////////////
// Sequential logic
/////////////////////////////////////////////////////

// Write ports
always @(posedge clk_a)
    if ((ce_a == `TRUE) && (we_a == `TRUE))
        mem[addr_a] <= di_a;

always @(posedge clk_b)
    if ((ce_b == `TRUE) && (we_b == `TRUE))
        mem[addr_b] <= di_b;

// Register read addresses for use on next cycle
always @(posedge clk_a)
    if (ce_a == `TRUE)
        ra_a <= addr_a;

always @(posedge clk_b)
    if (ce_b == `TRUE)
        ra_b <= addr_b;

/////////////////////////////////////////////////////
// Initialization
/////////////////////////////////////////////////////

generate
    if (init_file != "NONE")
    begin
initial $readmemh(init_file, mem);
    end
endgenerate
    
endmodule
