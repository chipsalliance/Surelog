// A named-field assignment pattern folded its field values against the module's
// DEFAULT parameters instead of the instance's overrides.
//
// `AxiSize` is a localparam over the module's `W`, which the parent overrides
// to 64.  Used DIRECTLY it was always correct (3).  Used as a field value
// inside `'{ ... size: AxiSize, ... }` it came out 1 -- $clog2(16/8), the
// DEFAULT -- because compileAssignmentPattern substituted a field that names a
// parameter with a hard-coded Reduce::Yes lookup, ignoring the Reduce::No its
// caller passes for a module body.  That resolves against the module
// DEFINITION, where the parameter still holds its default, and since the
// definition's cont_assigns are what every elaborated instance carries, the
// stale constant outlived the override.
//
// The elaborated parameter was always right (work@dut.u.AxiSize = UINT:3),
// which is why `plain_o` below always agreed and only `pat_o` was wrong.
//
// Found on PULP axi_lite_to_axi, whose
//   localparam AxiSize = axi_pkg::size_t'($unsigned($clog2(AxiDataWidth/8)));
//   assign mst_req_o = '{aw: '{size: AxiSize, ...}, ar: '{size: AxiSize, ...}};
// emitted aw.size/ar.size = 0 instead of 3.
package pk;
  typedef logic [2:0] size_t;
  typedef struct packed {
    logic [7:0] addr;
    size_t      size;
    logic [1:0] burst;
  } chan_t;
endpackage

module child #(parameter int unsigned W = 32'd16) (
  input  logic [7:0]  addr_i,
  output logic [2:0]  plain_o,   // AxiSize used directly        -> 3
  output logic [12:0] pat_o      // the same one as a pattern field -> was 1
);
  localparam int unsigned AxiSize = pk::size_t'($unsigned($clog2(W/8)));
  pk::chan_t c;
  assign plain_o = AxiSize;
  assign c = '{ addr: addr_i, size: AxiSize, burst: 2'b00, default: '0 };
  assign pat_o = c;
endmodule

module dut (
  input  logic [7:0]  addr_i,
  output logic [2:0]  plain_o,
  output logic [12:0] pat_o
);
  child #(.W(64)) u (.*);
endmodule
