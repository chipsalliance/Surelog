module top(i_clk,b);
input i_clk;
output b;

reg f_past_gbl_clock_valid;
initial f_past_gbl_clock_valid = 0;
always @(posedge i_clk)
  f_past_gbl_clock_valid <= 1'b1;
assign b = f_past_gbl_clock_valid;

endmodule
