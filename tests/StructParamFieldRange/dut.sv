// Reproducer: a struct-typed parameter whose field (`Cfg.XLEN`) is used in the
// member widths of a `localparam type` struct, then a `localparam` of that type
// is declared with an assignment pattern.  Elaborating the localparam runs
// ExprEval::flattenPatternAssignments, which clones the struct typespec; the
// cloned member range references the struct-typed parameter and was reported as
// UH0725 "Unresolved hierarchical reference Cfg.XLEN" (CVA6 core/cva6.sv
// interrupts_t / INTERRUPTS).  Fixed by reducing the struct member ranges with
// the instance's parameter values before flattening (NetlistElaboration).
package cfg_pkg;
  typedef struct packed {
    int unsigned XLEN;
    int unsigned VLEN;
  } cfg_t;
  localparam cfg_t DefaultCfg = '{XLEN: 32'd64, VLEN: 32'd64};
endpackage

module StructParamFieldRange #(
    parameter cfg_pkg::cfg_t Cfg = cfg_pkg::DefaultCfg
) (
    input  logic                a_i,
    output logic [Cfg.XLEN-1:0] b_o
);
  localparam type it_t = struct packed {
    logic [Cfg.XLEN-1:0] x;
    logic [Cfg.XLEN-1:0] y;
  };
  localparam it_t I = '{x: Cfg.XLEN'(1), y: Cfg.XLEN'(2)};
  assign b_o = a_i ? I.x : I.y;
endmodule
