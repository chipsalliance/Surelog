// An unpacked-array parameter whose ELEMENT TYPE is a packed struct, defaulted
// with '{default: <struct expression>}.
//
// defaultPatternAssignment resized the pattern value through an
// any_cast<constant*> without checking it.  A struct-valued default -- a
// parameter reference, or a nested assignment pattern -- is not a constant, so
// the cast yielded nullptr and the elaborator SEGFAULTED.  CV32E40X declares
// `parameter pma_cfg_t PMA_CFG[PMA_NUM_REGIONS-1:0] = '{default: PMA_R_DEFAULT}`
// and could not be elaborated at all.
package p;
  typedef struct packed {
    logic [7:0] lo;
    logic       main;
  } cfg_t;
  parameter cfg_t DEF = '{lo: 8'hA5, main: 1'b1};
endpackage

module dut
  import p::*;
#(
  parameter int   N           = 2,
  parameter cfg_t CFG [N-1:0] = '{default: DEF},
  parameter cfg_t CFG2[N-1:0] = '{default: '{lo: 8'h5A, main: 1'b0}}
)
(
  input  logic       en,
  output logic [8:0] y
);
  assign y = en ? {DEF.lo, DEF.main} : 9'h000;
endmodule
