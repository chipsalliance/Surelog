// Regression: a generate-for whose bound is a struct-parameter FIELD
// (`CFG.HSK.DLY`) must be elaborated even when the parameter comes from a
// localparam and/or a POSITIONAL struct initializer.  Surelog previously could
// not fold the bound (the value pattern carries no typespec, so a positional
// operand could not be indexed by name), so the whole generate block was
// silently dropped.  Mirrors the degu SoC tcb_lite_if delay line.
package p;
  typedef struct packed { int unsigned DLY; logic HLD; } hsk_t;
  typedef struct packed { hsk_t HSK; int unsigned DAT; } cfg_t;
  localparam cfg_t CFG_DEF = '{HSK: '{1, 1'b0}, DAT: 32};   // positional HSK
endpackage
interface bus_if #(parameter p::cfg_t CFG = p::CFG_DEF);
  logic dly [0:CFG.HSK.DLY];
  assign dly[0] = 1'b1;
  generate
    for (genvar i = 1; i <= CFG.HSK.DLY; i++) begin: g
      logic tmp;
      assign dly[i] = tmp;
      always_ff @(posedge dly[0]) tmp <= dly[i-1];
    end
  endgenerate
endinterface
module top (output logic o);
  import p::*;
  bus_if #(CFG_DEF) b ();
  assign o = b.dly[1];   // reads the delayed element (needs the generate block)
endmodule
