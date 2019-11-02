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


module vscale_alu(
                  input [4-1:0] op,
                  input [32-1:0]      in1,
                  input [32-1:0]      in2,
                  output reg [32-1:0] out
                  );

   wire [5-1:0]                  shamt;

   assign shamt = in2[5-1:0];

   always @(*) begin
      case (op)
         4'd0: out = in1 + in2;
         4'd1: out = in1 << shamt;
         4'd4: out = in1 ^ in2;
         4'd6: out = in1 | in2;
         4'd7: out = in1 & in2;
         4'd5: out = in1 >> shamt;
         4'd8: out = {31'b0, in1 == in2};
         4'd9: out = {31'b0, in1 != in2};
         4'd10: out = in1 - in2;
         4'd11: out = $signed(in1) >>> shamt;
         4'd12: out = {31'b0, $signed(in1) < $signed(in2)};
         4'd13: out = {31'b0, $signed(in1) >= $signed(in2)};
         4'd14: out = {31'b0, in1 < in2};
         4'd15: out = {31'b0, in1 >= in2};
        default : out = 0;
      endcase // case op
   end


endmodule // vscale_alu
