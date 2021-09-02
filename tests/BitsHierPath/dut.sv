package pkg;
  typedef struct packed {
    logic[7:0] x;
    logic      z;
  } struct_t;
endpackage : pkg

module dut #(parameter int Width = 1) ();
endmodule

module top (input pkg::struct_t in);
   localparam int SyncWidth = $bits({in,in.x});
   dut #(.Width($bits({in.x}))) dut1();
   dut #(.Width($bits({in}))) dut2();
   dut #(.Width($bits(in))) dut3();
   dut #(.Width($bits({in,in.x}))) dut4();
endmodule // top
