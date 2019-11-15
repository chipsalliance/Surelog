/*

Copyright (c) 2016 Alex Forencich

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.

*/

// Language: Verilog 2001

`timescale 1ns / 1ps

/*
 * Generic dual-port RAM
 */
module ram_dp #
(
    parameter DATA_WIDTH = 32,
    parameter ADDR_WIDTH = 10
)
(
    // port A
    input  wire                    a_clk,
    input  wire                    a_we,
    input  wire [ADDR_WIDTH-1:0]   a_addr,
    input  wire [DATA_WIDTH-1:0]   a_din,
    output wire [DATA_WIDTH-1:0]   a_dout,

    // port B
    input  wire                    b_clk,
    input  wire                    b_we,
    input  wire [ADDR_WIDTH-1:0]   b_addr,
    input  wire [DATA_WIDTH-1:0]   b_din,
    output wire [DATA_WIDTH-1:0]   b_dout
);

reg [DATA_WIDTH-1:0] a_dout_reg = {DATA_WIDTH{1'b0}};

reg [DATA_WIDTH-1:0] b_dout_reg = {DATA_WIDTH{1'b0}};

// (* RAM_STYLE="BLOCK" *)
reg [DATA_WIDTH-1:0] mem[(2**ADDR_WIDTH)-1:0];

assign a_dout = a_dout_reg;

assign b_dout = b_dout_reg;

integer i, j;

initial begin
    // two nested loops for smaller number of iterations per loop
    // workaround for synthesizer complaints about large loop counts
    for (i = 0; i < 2**ADDR_WIDTH; i = i + 2**(ADDR_WIDTH/2)) begin
        for (j = i; j < i + 2**(ADDR_WIDTH/2); j = j + 1) begin
            mem[j] = 0;
        end
    end
end

// port A
always @(posedge a_clk) begin
    a_dout_reg <= mem[a_addr];
    if (a_we) begin
        mem[a_addr] <= a_din;
        a_dout_reg <= a_din;
    end
end

// port B
always @(posedge b_clk) begin
    b_dout_reg <= mem[b_addr];
    if (b_we) begin
        mem[b_addr] <= b_din;
        b_dout_reg <= b_din;
    end
end

endmodule
