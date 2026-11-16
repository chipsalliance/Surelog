// IEEE 1800-2023 23.2.2.1: non-ANSI explicit port names.  A port's external
// name differs from its internal expression, which may be a concatenation or
// a part-select.
module sub(.bus({hi, lo}), .y(out[3:0]), .z(out[7:4]));
  input  [3:0] hi, lo;
  output [7:0] out;
  assign out = {hi ^ lo, hi & lo};
endmodule

module dut(input logic [7:0] bus, output logic [3:0] y, z);
  sub u(.bus(bus), .y(y), .z(z));
endmodule
