module tlul_fifo_sync #(parameter int unsigned ReqDepth = 2) ();
   logic [ReqDepth-1:0] storage;  
endmodule


module tlul_socket_1n #(
     parameter bit [75:0] DReqDepth = 76'h2000000000000000F)();
     parameter int unsigned ReqDepthKO = DReqDepth[8*4+:4];
     logic [ReqDepthKO-1:0] storageKO;  

     parameter int unsigned ReqDepthOK = DReqDepth[0+:4];
     logic [ReqDepthOK-1:0] storageOK; 

    tlul_fifo_sync #(
      .ReqDepth(DReqDepth[0+:4])
    ) fifo_d ();
 
endmodule


