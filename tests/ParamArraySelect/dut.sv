package otp_ctrl_pkg;
  typedef struct packed {
    logic [10:0] size;
  } part_info_t;
  parameter int NumPart = 2;  
endpackage // otp_ctrl_pkg


package otp_ctrl_part_pkg;
  import otp_ctrl_pkg::*;
  localparam part_info_t PartInfo [NumPart] = '{
    // CREATOR_SW_CFG
    '{
      size:       768,
      offset:     100
    }, 
    // LIFE_CYCLE
    '{
      size:       56,
      offset:     200
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

  if (NumLcOtpWords != 28) begin
     BAD bad();
  end
  
endmodule // otp_ctrl_lci


module top ();
  import otp_ctrl_part_pkg::*;
   
  otp_ctrl_lci #(
    .Info(PartInfo[LifeCycleIdx])
  ) u_otp_ctrl_lci ();

  parameter int OtpByteAddrWidth = 3;
  logic [PartInfo[LifeCycleIdx].size:0] aaa;

 for (genvar k = 0; k < NumPart; k++) begin : gen_part_sel
    localparam logic [OtpByteAddrWidth:0] PartEnd = (OtpByteAddrWidth+1)'(PartInfo[k].offset) +
                                                    (OtpByteAddrWidth+1)'(PartInfo[k].size);
   
    localparam logic [OtpByteAddrWidth-1:0] DigestOffset = OtpByteAddrWidth'(PartEnd -
                                                                             4);
  
  end

  
endmodule
