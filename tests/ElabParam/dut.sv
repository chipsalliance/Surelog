package top_pkg;
   typedef enum logic [5:0] {
     OPCODE_LOAD     = 6'h03,
     OPCODE_STORE    = 6'h13
   } opcode_e;
 
 parameter int unsigned PMP_CFG_W = 2;
 
 endpackage
 
 module dut (a, b);
   input [5:0] a;
   output [2:0] b;
   wire [5:0] a;
   reg [2:0] b;
   assign b = 4'(top_pkg::PMP_CFG_W)
              | 5'(a == top_pkg::OPCODE_LOAD);
 endmodule
 
