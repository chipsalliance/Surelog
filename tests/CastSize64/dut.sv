// A size cast of 64 bits or wider (`64'(X)`) folded to 0 in ExprEval
// (1ULL << 64 is undefined); constants derived from it were folded wrong too.
module dut (input logic [63:0] a, output logic [63:0] o, output logic [63:0] o2);
  localparam int unsigned BS = 512;
  localparam bit [63:0] C32 = 32'(BS);
  localparam bit [63:0] C63 = 63'(BS);
  localparam bit [63:0] C64 = 64'(BS);
  localparam bit [63:0] C65 = 65'(BS);
  localparam bit [63:0] D64 = 64'(BS) + 64'd256;   // 768
  assign o  = a + C32 + C63 + C64 + C65;            // a + 2048
  assign o2 = D64;
endmodule
