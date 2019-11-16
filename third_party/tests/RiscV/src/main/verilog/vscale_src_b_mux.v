`include "vscale_ctrl_constants.vh"
`include "rv32_opcodes.vh"

module vscale_src_b_mux(
                        input [`SRC_B_SEL_WIDTH-1:0] src_b_sel,
                        input [`XPR_LEN-1:0]         imm,
                        input [`XPR_LEN-1:0]         rs2_data,
                        output reg [`XPR_LEN-1:0]    alu_src_b
                        );


   always @(*) begin
      case (src_b_sel)
        `SRC_B_RS2 : alu_src_b = rs2_data;
        `SRC_B_IMM : alu_src_b = imm;
        `SRC_B_FOUR : alu_src_b = 4;
        default : alu_src_b = 0;
      endcase // case (src_b_sel)
   end

endmodule // vscale_src_b_mux
