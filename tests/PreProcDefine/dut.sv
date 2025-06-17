`define FOO(n)   n // comment
`define BAR     10'h03E

module top();
  wire  [9:0] a;
  assign a = `BAR;
endmodule