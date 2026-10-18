// $bits of an enum declared WITHOUT a base type is 32 (it is an int, IEEE
// 1800-2017 6.19); it folded to 0, and black-parrot's icache packet width
// `1 + vaddr_width_p + $bits(bp_fe_icache_op_e)` came out 40 instead of 72.
package p;
  typedef enum { e_a, e_b, e_c } op_e;
  typedef enum logic [1:0] { f_a, f_b } op2_e;
  localparam pkt_w = 1 + 7 + $bits(op_e);
endpackage
module top import p::*; #(localparam w_lp = 1 + 7 + $bits(op_e), localparam w2_lp = $bits(op2_e))
  (input logic [w_lp-1:0] a, input logic [w2_lp-1:0] b, output logic [w_lp-1:0] y, output logic [pkt_w-1:0] z, output logic [w2_lp-1:0] y2);
  assign y = ~a;
  assign z = a + 1;
  assign y2 = ~b;
endmodule
