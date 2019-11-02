module mux_x(clk, in, en, out);
   input clk, in, en;
   output out;

   assign out = en ? in : 1'bx;

endmodule // latchx
