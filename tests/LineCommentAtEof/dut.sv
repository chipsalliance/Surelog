// defs.vh ends in a `define whose line comment runs to EOF (no final
// newline), like OpenPiton's chipset/include/uart16550_define.vh.  The
// comment must not be part of the macro body: `LSR_DR is 0, and both uses
// below parse.
`include "defs.vh"
module dut(input logic [7:0] d, input logic v, output logic a, b);
  assign a = v & d[`LSR_DR];
  assign b = v & ~d[`LSR_DR];
endmodule
