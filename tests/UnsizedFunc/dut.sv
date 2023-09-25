

module prim_lfsr(output int o);
   parameter int unsigned LfsrDw = 12;
   function automatic logic [LfsrDw-1:0] get_1s();
      logic [LfsrDw-1:0] a = '1;
      return a;
   endfunction

   initial begin
      o = int'(get_1s());
   end
endmodule

module top(output int o);
   prim_lfsr #(
      .LfsrDw(16)
   ) u_lfsr(.o(o));
endmodule

/*
package sha3_pkg;
  parameter int MsgWidth = 64;
  parameter int MsgStrbW = MsgWidth / 8;
endpackage


package kmac_pkg;
  parameter int MsgWidth = sha3_pkg::MsgWidth;
  parameter int MsgStrbW = sha3_pkg::MsgStrbW;
  parameter int RegIntfWidth = 32; // 32bit interface
  parameter int RegLatency   = 5;  // 5 cycle to write one Word
  parameter int Sha3Latency  = 72; // Expected masked sha3 processing time 24x3

  // Total required buffer size while SHA3 is in processing
  parameter int BufferCycles   = (Sha3Latency + RegLatency - 1)/RegLatency;
  parameter int BufferSizeBits = RegIntfWidth * BufferCycles;
   parameter int MsgFifoDepth   = 2 + ((BufferSizeBits + MsgWidth - 1)/MsgWidth);
   parameter int MsgFifoDepthW  = $clog2(MsgFifoDepth+1);
endpackage


module prim_fifo_sync #(
  parameter int unsigned Width       = 16,
  parameter bit Pass                 = 1'b1, // if == 1 allow requests to pass through empty FIFO
  parameter int unsigned Depth       = 4,
  parameter bit OutputZeroIfEmpty    = 1'b1, // if == 1 always output 0 when FIFO is empty
  // derived parameter
  localparam int unsigned DepthWNorm = $clog2(Depth+1),
  localparam int unsigned DepthW     = (DepthWNorm == 0) ? 1 : DepthWNorm
) (output  [DepthW-1:0]    depth);

assign depth = 1'b0;


endmodule

module kmac_msgfifo
  import kmac_pkg::*;
#(
  // OutWidth is MsgFIFO data width. prim_packer converts InW to OutW prior to
  // pushing to MsgFIFO
  parameter int OutWidth = 64,

  // Internal MsgFIFO Entry count
  parameter  int MsgDepth = 9,
  localparam int MsgDepthW = $clog2(MsgDepth+1) // derived parameter
) (
    output logic [MsgDepthW-1:0] fifo_depth_o);

    typedef struct packed {
        logic [OutWidth-1:0]   data;
        logic [OutWidth/8-1:0] strb; // one bit per byte
      } fifo_t;
     
    prim_fifo_sync #(
        .Width ($bits(fifo_t)),
        .Pass  (1'b 1),
        .Depth (MsgDepth)
      ) u_msgfifo (
        .depth (fifo_depth_o)
      );


endmodule

module kmac ();

logic [kmac_pkg::MsgFifoDepthW-1:0] msgfifo_depth;

assign o = msgfifo_depth;

kmac_msgfifo #(
    .OutWidth (kmac_pkg::MsgWidth),
    .MsgDepth (kmac_pkg::MsgFifoDepth)
  ) u_msgfifo (
   
    .fifo_depth_o (msgfifo_depth)
  );


endmodule
*/