module top(i_clk,b);
input i_clk;
output b;

wire value = 0;


reg f_past_gbl_clock_valid;
initial f_past_gbl_clock_valid = 0;
always @(posedge i_clk)
  f_past_gbl_clock_valid <= 1'b1;

always @(posedge i_clk)
  if ((f_past_gbl_clock_valid)&&(!$rose(i_clk)))
  begin
     assert($stable(value));
  end

assign b = f_past_gbl_clock_valid;

endmodule
