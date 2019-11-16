`include "vscale_ctrl_constants.vh"
`include "rv32_opcodes.vh"

module vscale_imm_gen(
                      input [`XPR_LEN-1:0]        inst,
                      input [`IMM_TYPE_WIDTH-1:0] imm_type,
                      output reg [`XPR_LEN-1:0]   imm
                      );

   always @(*) begin
      case (imm_type)
        `IMM_I : imm = { {21{inst[31]}}, inst[30:25], inst[24:21], inst[20] };
        `IMM_S : imm = { {21{inst[31]}}, inst[30:25], inst[11:8], inst[7] };
        `IMM_U : imm = { inst[31], inst[30:20], inst[19:12], 12'b0 };
        `IMM_J : imm = { {12{inst[31]}}, inst[19:12], inst[20], inst[30:25], inst[24:21], 1'b0 };
        default : imm = { {21{inst[31]}}, inst[30:25], inst[24:21], inst[20] };
      endcase // case (imm_type)
   end

endmodule // vscale_imm_gen




