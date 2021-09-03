
module tlul_fifo_sync #(parameter int unsigned ReqDepth) ();
endmodule

module tlul_socket_1n #(parameter int unsigned N, parameter bit [N*4-1:0] DReqDepth) ();
  for (genvar i = 0 ; i < N ; i++) begin : gen_dfifo
    tlul_fifo_sync #(.ReqDepth(DReqDepth[i*4+:4])) fifo_d();
  end
endmodule

module xbar_main;
  tlul_socket_1n #(.DReqDepth (68'h200000000000000), .N(8)) u_s1n_25();
endmodule


module top();

 parameter A = 68'h200000000000000;
 parameter B = A[8*4+:4];

endmodule // top
