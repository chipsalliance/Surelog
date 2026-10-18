// A concatenation fold must extend a wildcard literal with its leftmost digit
// (IEEE 1800-2017 5.7.1): `{64'b????????????????}` means every address, and
// zero-extended it matched only the low 64 KiB (black-parrot bp_sacc_vdp's
// register decode via base_addr_p({64'b????????????????})).
module reg_dec #(parameter els_p = 1, parameter reg_addr_width_p = 40,
                 parameter [els_p-1:0][reg_addr_width_p-1:0] base_addr_p = '0)
  (input logic [reg_addr_width_p-1:0] addr, output logic [els_p-1:0] m);
  for (genvar i = 0; i < els_p; i++) begin : dec
    assign m[i] = addr inside {base_addr_p[i]};
  end
endmodule
module top (input logic [39:0] addr, output logic m1, output logic [1:0] m2);
  reg_dec #(.els_p(1), .reg_addr_width_p(40), .base_addr_p({64'b????????????????})) r1 (.addr(addr), .m(m1));
  reg_dec #(.els_p(2), .reg_addr_width_p(40), .base_addr_p({40'h8???, 40'b1???})) r2 (.addr(addr), .m(m2));
endmodule
