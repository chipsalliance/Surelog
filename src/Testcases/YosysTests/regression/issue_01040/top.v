module dut_sub(input clk, input [32:2] a, output [32:2] a_l);

always @(posedge clk) a_l <= a;

endmodule // dut_sub


module dut(input clk, input[32:2] a, output [32:2] a_l);

dut_sub sub(.clk(clk), .a(a), .a_l(a_l));

endmodule // dut
