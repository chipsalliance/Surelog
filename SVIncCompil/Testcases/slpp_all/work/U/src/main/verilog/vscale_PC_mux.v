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


module vscale_PC_mux(
                     input [3-1:0] PC_src_sel,
                     input [32-1:0]       inst_DX,
                     input [32-1:0]          rs1_data,
                     input [32-1:0]          PC_IF,
                     input [32-1:0]          PC_DX,
                     input [32-1:0]          handler_PC,
                     input [32-1:0]          epc,
                     output [32-1:0]         PC_PIF
                     );

   wire [32-1:0]                             imm_b = { {20{inst_DX[31]}}, inst_DX[7], inst_DX[30:25], inst_DX[11:8],  1'b0};
   wire [32-1:0]                             jal_offset = { {12{inst_DX[31]}}, inst_DX[19:12], inst_DX[20], inst_DX[30:25], inst_DX[24:21],  1'b0};
   wire [32-1:0]                             jalr_offset = { {21{inst_DX[31]}}, inst_DX[30:21],  1'b0};

   reg [32-1:0]                              base;
   reg [32-1:0]                              offset;

   always @(*) begin
      case (PC_src_sel)
         3'd2: begin
           base = PC_DX;
           offset = jal_offset;
        end
         3'd3: begin
           base = rs1_data;
           offset = jalr_offset;
        end
         3'd1: begin
           base = PC_DX;
           offset = imm_b;
        end
         3'd4: begin
           base = PC_IF;
           offset = 32'h0;
        end
         3'd5: begin
           base = handler_PC;
           offset = 32'h0;
        end
         3'd6: begin
           base = epc;
           offset = 32'h0;
        end
        default : begin
           base = PC_IF;
           offset = 32'h4;
        end
      endcase // case (PC_src_sel)
   end // always @ (*)

   assign PC_PIF = base + offset;


endmodule // vscale_PC_mux

