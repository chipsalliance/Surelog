package pkg;
  typedef struct packed {
    logic a;
    logic [2:0] b;
  } complex_t;
endpackage


module top ();
   localparam pkg::complex_t init_val = '{a: 1'b0, b: '1};
   dut #(
       .size ($bits(pkg::complex_t)),
       .init ({init_val})
     ) asgn0();
endmodule

module dut #(
    parameter int size = 0,
    parameter bit [size-1:0] init = '0
  ) ();

endmodule // dut
