// Width-related constants


// Opcodes



// 7'b1101011 is reserved



// 7'b1010111 is reserved
// 7'b1110111 is reserved

// 7'b0011011 is RV64-specific
// 7'b0111011 is RV64-specific

// Arithmetic FUNCT3 encodings


// Branch FUNCT3 encodings


// MISC-MEM FUNCT3 encodings

// SYSTEM FUNCT3 encodings


// PRIV FUNCT12 encodings


// RV32M encodings


module vscale_src_b_mux(
                        input [2-1:0] src_b_sel,
                        input [32-1:0]         imm,
                        input [32-1:0]         rs2_data,
                        output reg [32-1:0]    alu_src_b
                        );


   always @(*) begin
      case (src_b_sel)
         2'd0: alu_src_b = rs2_data;
         2'd1: alu_src_b = imm;
         2'd2: alu_src_b = 4;
        default : alu_src_b = 0;
      endcase // case (src_b_sel)
   end

endmodule // vscale_src_b_mux
