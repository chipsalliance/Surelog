module top();
  logic a = 1;
  initial assert  #0 (a != 0);
endmodule // top
