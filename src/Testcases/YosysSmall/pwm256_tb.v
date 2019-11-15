// Testbench for 256-level PWM generator
// Author: Niels A. Moseley
//         Symbiotic EDA / Moseley Instruments
//         10-11-2018

module tb;

reg  clk   = 0;
reg  rst_n = 0;
reg  [7:0] d_in  = 8'd128;
wire pwm;

// clock generation
always #1 clk=~clk;

// devices under test
pwm256 dut(clk, rst_n, d_in, pwm);

initial
begin
    $dumpfile("pwm256_tb.vcd");
    $dumpvars;

    #4 rst_n = 1'b1;
    #516 d_in = 8'd10;
    #1028 d_in = 8'd246;
    #1540 $finish;
    
end

endmodule