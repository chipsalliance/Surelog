package p;
  typedef struct packed { logic [63:0] PAD0; logic [8:0] BTB_ADDR_HI; logic [4:0] BTB_BTAG_FOLD; logic [8:0] BTB_BTAG_SIZE; logic [4:0] BTB_FULLYA; logic [63:0] PAD1; } cfg_t;
  localparam cfg_t CFG = '{PAD0: 64'hFFFF_0000_FFFF_0000, BTB_ADDR_HI: 9'd9, BTB_BTAG_FOLD: 5'd0, BTB_BTAG_SIZE: 9'd5, BTB_FULLYA: 5'd0, PAD1: 64'h1234_5678_9abc_def0};
endpackage
module dut import p::*; #(parameter cfg_t pt = CFG) (input logic [31:1] firstpc, output logic [pt.BTB_BTAG_SIZE-1:0] btag);
  if (pt.BTB_FULLYA) begin
    assign btag = firstpc[pt.BTB_BTAG_SIZE:1];
  end else begin
    if (pt.BTB_BTAG_FOLD) begin : btbfold_en
      assign btag = firstpc[9:5] ^ firstpc[4:0];
    end else begin : btbfold
      assign btag = firstpc[24:20] ^ firstpc[19:15] ^ firstpc[14:10];
    end
  end
endmodule
