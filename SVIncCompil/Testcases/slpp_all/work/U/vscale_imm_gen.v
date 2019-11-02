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


module vscale_imm_gen(
                      input [32-1:0]        inst,
                      input [2-1:0] imm_type,
                      output reg [32-1:0]   imm
                      );

   always @(*) begin
      case (imm_type)
         2'd0: imm = { {21{inst[31]}}, inst[30:25], inst[24:21], inst[20] };
         2'd1: imm = { {21{inst[31]}}, inst[30:25], inst[11:8], inst[7] };
         2'd2: imm = { inst[31], inst[30:20], inst[19:12],  12'b0};
         2'd3: imm = { {12{inst[31]}}, inst[19:12], inst[20], inst[30:25], inst[24:21],  1'b0};
        default : imm = { {21{inst[31]}}, inst[30:25], inst[24:21], inst[20] };
      endcase // case (imm_type)
   end

endmodule // vscale_imm_gen




