// IEEE 1800-2023 33.4: a configuration selects, per instance, which module
// definition binds to an instantiation.  Here `u_op` instantiates `op_add`,
// and the config rebinds it to `op_xor`; the default binding stays for u_ref.
module op_add(input logic [7:0] a, b, output logic [7:0] y);
  assign y = a + b;
endmodule

module op_xor(input logic [7:0] a, b, output logic [7:0] y);
  assign y = a ^ b;
endmodule

module dut(input logic [7:0] a, b, output logic [7:0] y, r);
  op_add u_op (.a(a), .b(b), .y(y));
  op_add u_ref(.a(a), .b(b), .y(r));
endmodule

config cfg;
  design work.dut;
  default liblist work;
  instance dut.u_op use work.op_xor;
endconfig
