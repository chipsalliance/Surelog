module bar(clk, rst, inp, out);
  input  wire clk;
  input  wire rst;
  input  wire inp;
  output reg  out;

  always @(posedge clk)
    if (rst) out <= 1'd0;
    else     out <= ~inp;

endmodule

module foo(clk, rst, inp, out);
  input  wire clk;
  input  wire rst;
  input  wire inp;
  output wire out;

  bar bar_instance ( (* clock_connected  = 1'b1 *) clk, rst, (* this_is_the_input  = "foo" *) inp, out);
endmodule

