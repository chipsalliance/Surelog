module top (input [2:0] s, input [5:0] a, output y);
  assign y = a[s];
endmodule
