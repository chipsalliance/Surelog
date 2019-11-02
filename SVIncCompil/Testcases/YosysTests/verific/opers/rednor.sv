module top (input [6:0] a, output y);
  assign y = ~|a;
endmodule
