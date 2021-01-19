
module prim_fifo_sync #(
  parameter int unsigned Depth       = 4
) (
);

  // FIFO is in complete passthrough mode
  if (Depth == 0) begin : gen_passthru
   

    assign depth = 1'b0; //output is meaningless

   
  // Normal FIFO construction
  end else begin : gen_normal

    // consider Depth == 1 case when $clog2(1) == 0
    localparam int unsigned PTRV_W    = $clog2(Depth) + ~|$clog2(Depth);
   
  end
endmodule


module fifo_sync #(
  parameter int unsigned ReqDepth = 6
) (
);


  prim_fifo_sync #(.Depth(ReqDepth)) reqfifo ();


endmodule




module socket_1n #(
  parameter int unsigned  N         = 2,
  parameter bit [7:0] DReqDepth = {N{4'h2}}) ();
  parameter bit [7:0] AA = DReqDepth * 2;
  parameter bit [7:0] BB = DReqDepth[1*4+:4];
  
  for (genvar i = 0 ; i < N ; i++) begin : gen_dfifo
    fifo_sync #(
      .ReqDepth(DReqDepth[i*4+:4])
    ) fifo_d ();
  end


endmodule;


module all_zero #(
  parameter int unsigned  N         = 2,
  parameter bit [7:0] DReqDepth = {2{4'h0}}) ();
  parameter bit [7:0] AA = DReqDepth * 2;
  parameter bit [7:0] BB = DReqDepth[1*4+:4];
  
  for (genvar i = 0 ; i < N ; i++) begin : gen_dfifo
    fifo_sync #(
      .ReqDepth(DReqDepth[i*4+:4])
    ) fifo_d ();
  end


endmodule;
