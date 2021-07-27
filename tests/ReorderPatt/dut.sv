module top();
   parameter int x [1:0] = '{10, 11};
   parameter a = x[0];
   assign b = x[0];
endmodule
