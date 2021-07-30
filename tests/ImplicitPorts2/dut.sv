module implicit();
  reg clk;
  wire q;

  // Here second port is not connected
  dff u0 ( q,,clk); 

endmodule

// D fli-flop
module dff (q, q_bar, clk);
  input clk;
  output q, q_bar;
  reg q;
endmodule
