// Testbench for 5th order CIC filter with decimation factor of 5
// Author: Niels A. Moseley
//         Symbiotic EDA / Moseley Instruments
//
// 12-11-2018


module tb;

reg  clk   = 0;
reg  rst_n = 0;
reg  signed [15:0] d_in = 0;
wire signed [27:0] d_out = 0;
wire d_out_valid;

// clock generation
always #1 clk=~clk;

// devices under test
cic5 dut(clk, rst_n, d_in, d_out, d_out_valid);

initial
begin
    $dumpfile("cic5_tb.vcd");
    $dumpvars;
    d_in     <= 16'h7fff;
    #4 rst_n = 1'b1;
    #60 d_in <= -16'h7fff;
    #60 $finish;
end

endmodule