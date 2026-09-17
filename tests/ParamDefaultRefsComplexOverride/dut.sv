// A parameter whose DEFAULT references another parameter of the same module
// (`parameter CW = AW`) must follow AW's OVERRIDE, not AW's definition default.
//
// When the override is an expression the reducer cannot fold -- here a $clog2
// over a 96-bit concatenation, the shape of caliptra-rtl's
// `CALIPTRA_SLAVE_ADDR_WIDTH(n)` macro over 19 x 32-bit base/mask words -- AW
// has no simple Value on the instance, only a complex one.  The default `CW =
// AW` compiled to that same unreducible expression, and evalExpr, which cannot
// see complex values, then resolved AW to the DEFINITION default (32) and
// stored a valid, wrong constant: the child's `o` port came out 32 bits wide
// where AW is 13.  caliptra's ahb_slv_sif hit this as
// `CLIENT_ADDR_WIDTH = AHB_ADDR_WIDTH` -> 32 instead of 13.
//
// Expected: child.CW == child.AW == 13 (read_slang agrees).
`define BASE {32'h2000_5000, 32'h2000_4000, 32'h1004_0000}
`define MASK {32'h2000_5FFF, 32'h2000_4FFF, 32'h1004_1FFF}
`define AMASK (`BASE ^ `MASK)
`define W(n) $clog2((`AMASK >> (32*n)) & {32{1'b1}})

module child #(parameter AW = 32, parameter CW = AW)
  (input logic [AW-1:0] a, output logic [CW-1:0] o);
  assign o = a;
endmodule

module dut (input logic [12:0] a, output logic [12:0] o);
  // 96-bit operand: three 32-bit words, same shape as caliptra's 608-bit one.
  child #(.AW(`W(0))) u (.a(a), .o(o));
endmodule
