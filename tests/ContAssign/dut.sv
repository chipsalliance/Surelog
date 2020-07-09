module top();

  wire intf intf2  [2];

  wire ena = ~|clkcnt;

  wire #0.1 __debug_req_ready = debug_req_ready;
  
  wire toto;

  assign a = b;


endmodule
