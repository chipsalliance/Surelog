// Guards two definition-time elaboration-diagnostic fixes:
//  1. A module-scope $error must fire only when the module is INSTANTIATED,
//     not for a definition that is excluded in this configuration.
//  2. A typedef whose range divides by a parameter (`logic [64/N-1:0]`) is
//     bound (ElaborationStep::bindTypedefs_) with the module's DEFAULT param
//     value (N=0) -> a divide-by-zero that must be muted; the real range is
//     computed per-instance with the overriding value (N=8).
module dut #(parameter int N = 0) (output logic [7:0] o);
  typedef logic [64/N-1:0] word_t;
  word_t w;
  assign w = '0;
  assign o = w[7:0];
endmodule

module unused_stub #(parameter int M = 0) (output logic e);
  // Never instantiated in this configuration -> $error must NOT fire.
  $error("unused_stub: this stub must not be elaborated");
  assign e = 1'b0;
endmodule

module used_stub (output logic e);
  // Instantiated below -> $error MUST fire.
  $error("used_stub: instantiated stub error");
  assign e = 1'b0;
endmodule

module ElabDefinitionDiagnostics;
  logic [7:0] o;
  logic       e;
  dut #(.N(8)) i_dut (.o(o));
  used_stub    i_used (.e(e));
endmodule
