package pkg;
  parameter int Width      = 64;
  typedef logic [Width-1:0]   key;
  typedef struct packed {
    key   key;
  } init_t;
  localparam init_t InitDefault = '1;
endpackage

module foo2 #(parameter logic [63:0] ResetValue = '0)();
endmodule

module foo #(parameter logic [63:0] ResetValue = '0) ();
  foo2 #(.ResetValue(ResetValue)) f();
endmodule

module dut import pkg::*; #(parameter init_t Init = InitDefault) ();
  foo #(.ResetValue(Init.key)) f ();
endmodule

module top();
  dut d();
endmodule
