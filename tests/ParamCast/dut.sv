package  otp_ctrl_part_pkg;
 
typedef enum {
    CreatorSwCfgIdx,
    Blah,
    Boo,
    NumAgentsIdx
  } part_idx_e;
   
 parameter int NumAgents = int'(NumAgentsIdx);

endpackage


module otp_ctrl();
  import otp_ctrl_part_pkg::*;
  logic [NumAgents-1:0]    part_otp_arb_req;
endmodule
