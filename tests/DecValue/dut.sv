module top(output int o);
   parameter A = 'x;
   parameter B = 'x;
   localparam int C = A / B;

   assign o = int'(C);
endmodule // top

