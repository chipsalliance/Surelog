// Testbench for sddac.v
// Author: Niels A. Moseley

`include "constants.vams"

module tb;

reg  clk   = 0;
reg  rst_n = 0;
reg  [1:0] opcode = 2'b11;      // nop
reg  signed [15:0] a_bus = 0;
reg  signed [15:0] b_bus = 0;
wire signed [39:0] result;

// clock generation
always #1 clk=~clk;

// devices under test
dspmac_16_40 dut(clk, rst_n, opcode, a_bus, b_bus, result);

initial
begin
    $dumpfile("dspmac_16_40_tb.vcd");
    $dumpvars;

    opcode = 2'b00;     //CLR

    #4 rst_n = 1'b1;
    a_bus    = 16'd32767;
    b_bus    = 16'd32767;
    opcode   = 2'b01;       // MUL
    #2 opcode   = 2'b10;    // MAC
    #2 opcode   = 2'b11;    // NOP
    #2 opcode   = 2'b11;    // NOP
    #2 $finish;
    
end

endmodule