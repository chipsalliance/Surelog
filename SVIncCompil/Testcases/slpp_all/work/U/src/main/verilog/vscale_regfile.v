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


module vscale_regfile(
                      input                       clk,
                      input [5-1:0] ra1,
                      output [32-1:0]       rd1,
                      input [5-1:0] ra2,
                      output [32-1:0]       rd2,
                      input                       wen,
                      input [5-1:0] wa,
                      input [32-1:0]        wd
                      );

   reg [32-1:0]                             data [31:0];
   wire                                           wen_internal;

   // fpga-style zero register
   assign wen_internal = wen && |wa;

   assign rd1 = |ra1 ? data[ra1] : 0;
   assign rd2 = |ra2 ? data[ra2] : 0;

   always @(posedge clk) begin
      if (wen_internal) begin
         data[wa] <= wd;
      end
   end

   integer i;
   initial begin
      for (i = 0; i < 32; i = i + 1) begin
         data[i] = $random;
      end
   end

endmodule // vscale_regfile
