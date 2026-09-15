// $bits(arr[k].member) with a genvar index in a parameter override
// (OpenTitan keymgr_input_checks): no spurious UHDM_UNRESOLVED_HIER_PATH.
package p_pkg;
  typedef struct packed {
    logic [15:0] data;
    logic        valid;
  } kd_t;
endpackage
module ext #(parameter int InWidth = 1, parameter int OutWidth = 32) (
  input  logic [InWidth-1:0]  in_i,
  output logic [OutWidth-1:0] out_o
);
  assign out_o = OutWidth'(in_i);
endmodule
module top #(parameter int N = 2) (
  input  p_pkg::kd_t [N-1:0] rom_digest_i,
  output logic [N-1:0][31:0] padded_o
);
  for (genvar k = 0; k < N; k++) begin : gen_pad
    ext #(
      .InWidth($bits(rom_digest_i[k].data)),
      .OutWidth(32)
    ) u_pad (
      .in_i(rom_digest_i[k].data),
      .out_o(padded_o[k])
    );
  end
endmodule
