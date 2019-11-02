`include "vscale_ctrl_constants.vh"
`include "rv32_opcodes.vh"

module vscale_src_a_mux(
                        input [`SRC_A_SEL_WIDTH-1:0] src_a_sel,
                        input [`XPR_LEN-1:0]         PC_DX,
                        input [`XPR_LEN-1:0]         rs1_data,
                        output reg [`XPR_LEN-1:0]    alu_src_a
                        );


   always @(*) begin
      case (src_a_sel)
        `SRC_A_RS1 : alu_src_a = rs1_data;
        `SRC_A_PC : alu_src_a = PC_DX;
        default : alu_src_a = 0;
      endcase // case (src_a_sel)
   end

endmodule // vscale_src_a_mux
