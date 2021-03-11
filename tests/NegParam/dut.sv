module top();
 localparam dram_base_addr_gp         = 40'h00_8000_0000;
 
 localparam bp_proc_param_s bp_default_cfg_p =
    '{
      boot_pc       : dram_base_addr_gp
    };

endmodule

module prim_packer #(
  parameter int InW  = 32,
  parameter int OutW = 32,
  parameter int HintByteData = 0 // If 1, The input/output are byte granularity
) (
);

  localparam int Width = InW + OutW; // storage width
  localparam int ConcatW = Width + InW; // Input concatenated width
  localparam int PtrW = $clog2(ConcatW+1);
  localparam int IdxW = $clog2(InW) + ~|$clog2(InW);
  logic [PtrW-1:0]          pos, pos_next; // Current write position
  logic [IdxW-1:0]          lod_idx;       // result of Leading One Detector

  if (IdxW != 5) begin
    BAD bad();

  end


endmodule
