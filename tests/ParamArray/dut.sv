package otp_ctrl_pkg;
  typedef struct packed {
    logic [10:0] size;
  } part_info_t;
  parameter int NumPart = 7;  
endpackage // otp_ctrl_pkg


package otp_ctrl_part_pkg;
  import otp_ctrl_pkg::*;
  localparam part_info_t PartInfo [NumPart] = '{
    // CREATOR_SW_CFG
    '{
      size:       768
    }, 
    // LIFE_CYCLE
    '{
      size:       56
    }
  };

  typedef enum {
    CreatorSwCfgIdx,
    LifeCycleIdx
  } part_idx_e;

endpackage
 
module otp_ctrl_lci
  import otp_ctrl_pkg::*;
#(
  // Lifecycle partition information
  parameter part_info_t Info = part_info_t'(0)
  )  ();

 localparam int NumLcOtpWords = Info.size >> 1;

 logic [NumLcOtpWords-1:0] cnt_d;
  
endmodule // otp_ctrl_lci


module top ();
  import otp_ctrl_part_pkg::*;
   
  otp_ctrl_lci #(
    .Info(PartInfo[LifeCycleIdx])
  ) u_otp_ctrl_lci ();
   
endmodule
