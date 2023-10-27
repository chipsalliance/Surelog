package sha3_pkg;
  parameter int MsgWidth = 64;
endpackage : sha3_pkg

package kmac_pkg;
  parameter int MsgWidth = sha3_pkg::MsgWidth;
  parameter int RegIntfWidth = 32; // 32bit interface
  parameter int RegLatency   = 5;  // 5 cycle to write one Word
  parameter int Sha3Latency  = 72; // Expected masked sha3 processing time 24x3
  parameter int BufferCycles   = (Sha3Latency + RegLatency - 1)/RegLatency;
  parameter int BufferSizeBits = RegIntfWidth * BufferCycles;
  // Required MsgFifoDepth. Adding slightly more buffer for margin
  parameter int MsgFifoDepth   = 2 + ((BufferSizeBits + MsgWidth - 1)/MsgWidth);
  parameter int MsgFifoDepthW  = $clog2(MsgFifoDepth+1);
endpackage : kmac_pkg

package kmac_reg_pkg;
  typedef struct packed {
    struct packed {
      logic        d;
    } sha3_idle;
    struct packed {
      logic [4:0]  d;
    } fifo_depth;
  } kmac_hw2reg_status_reg_t;

  typedef struct packed {
    kmac_hw2reg_status_reg_t intr_state; 
    kmac_hw2reg_status_reg_t status;
  } kmac_hw2reg_t;
endpackage

module top();
  import kmac_pkg::*;
  import kmac_reg_pkg::*;
kmac_hw2reg_t hw2reg;
if ($bits(hw2reg.status.fifo_depth.d) != MsgFifoDepthW+1) begin : gen_fifo_depth_tie
    $error("ERROR both terms are supposed to be 5 !!!");
end
endmodule
