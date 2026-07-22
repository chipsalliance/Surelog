// Minimal repro of CVA6 core/cva6.sv `INTERRUPTS`: a struct-typed parameter
// whose value comes from a constant FUNCTION (like build_config), so the field
// `Cfg.XLEN` is not a plain struct-literal member.  `Cfg.XLEN` then appears in
// the CAST size and SHIFT operands of an assignment-pattern initializer.
// flattenPatternAssignments deep-clones these init expressions; the cast
// typespec range `[Cfg.XLEN-1:0]` and the shift operand `(Cfg.XLEN-1)` must be
// reduced to constants first, else the detached clone reports
// UHDM_UNRESOLVED_HIER_PATH (UH0725) -- NetlistElaboration reduceExprTree.
package cfg_pkg;
  typedef struct packed {
    int unsigned XLEN;
  } user_cfg_t;
  typedef struct packed {
    int unsigned XLEN;
  } cfg_t;
  function automatic cfg_t build_config(user_cfg_t c);
    cfg_t r;
    r.XLEN = c.XLEN;
    return r;
  endfunction
  localparam user_cfg_t Base = '{XLEN: 32'd64};
endpackage

module StructParamPatternInitCast #(
    parameter cfg_pkg::cfg_t Cfg = cfg_pkg::build_config(cfg_pkg::Base)
) (
    input  logic                a_i,
    output logic [Cfg.XLEN-1:0] b_o
);
  localparam type it_t = struct packed {
    logic [Cfg.XLEN-1:0] S_SW;
    logic [Cfg.XLEN-1:0] M_SW;
  };
  localparam it_t INT = '{
      S_SW: (Cfg.XLEN'(1) << (Cfg.XLEN - 1)) | Cfg.XLEN'(1),
      M_SW: (Cfg.XLEN'(1) << (Cfg.XLEN - 1)) | Cfg.XLEN'(3)
  };
  assign b_o = a_i ? INT.S_SW : INT.M_SW;
endmodule
