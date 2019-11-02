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


module vscale_src_a_mux(
                        input [2-1:0] src_a_sel,
                        input [32-1:0]         PC_DX,
                        input [32-1:0]         rs1_data,
                        output reg [32-1:0]    alu_src_a
                        );


   always @(*) begin
      case (src_a_sel)
         2'd0: alu_src_a = rs1_data;
         2'd1: alu_src_a = PC_DX;
        default : alu_src_a = 0;
      endcase // case (src_a_sel)
   end

endmodule // vscale_src_a_mux
