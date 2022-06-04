package swerv_types;

typedef struct packed {
                       logic [2:0] trace_rv_i_valid_ip;
                       logic [95:0] trace_rv_i_insn_ip;
                       } trace_pkt_t;

endpackage // swerv_types
   
module top();
  import swerv_types::*;
  trace_pkt_t  trace_rv_trace_pkt;
  assign trace_rv_i_insn_ip[63:0]     = trace_rv_trace_pkt.trace_rv_i_insn_ip[63:0];
endmodule
