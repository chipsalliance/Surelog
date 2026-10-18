// `T[1][i]` on a 3-D packed parameter OVERRIDDEN with a package constant that
// is a concatenation of concatenations: element selection must follow the
// declared dimension order, not the operand order as written.  black-parrot's
// bsg_wormhole_router read its routing matrix from the wrong half with the
// rows reversed when bp_nd_socket passed `.routing_matrix_p(StrictYX)`.
package rp;
  localparam bit [1:0][2:0][2:0] TA = { {3'b011, 3'b101, 3'b111}, {3'b100, 3'b010, 3'b000} };
  localparam bit [1:0][2:0][2:0] TB = { {3'b100, 3'b010, 3'b000}, {3'b011, 3'b101, 3'b111} };
endpackage
module rtr import rp::*; #(parameter sel_p = 0, parameter bit [1:0][2:0][2:0] mat_p = (sel_p == 0) ? TA : TB)
  (output logic [2:0][2:0] row1, output logic [2:0][2:0] row0, output logic [2:0][1:0] cnt);
  for (genvar i = 0; i < 3; i++) begin : g
    localparam ones_lp = mat_p[1][i][0] + mat_p[1][i][1] + mat_p[1][i][2];
    assign row1[i] = mat_p[1][i];
    assign row0[i] = mat_p[0][i];
    assign cnt[i] = ones_lp;
  end
endmodule
module mid import rp::*; #(parameter sel_p = 0, parameter bit [1:0][2:0][2:0] mat_p = (sel_p == 0) ? TA : TB)
  (output logic [2:0][2:0] row1, output logic [2:0][2:0] row0, output logic [2:0][1:0] cnt);
  rtr #(.sel_p(sel_p), .mat_p(mat_p)) r (.row1(row1), .row0(row0), .cnt(cnt));
endmodule
module top import rp::*; (output logic [2:0][2:0] a1, a0, b1, b0, c1, c0, output logic [2:0][1:0] ca, cb, cc);
  mid #(.sel_p(1)) m_default (.row1(a1), .row0(a0), .cnt(ca));            // default ternary -> TB
  mid #(.sel_p(0), .mat_p(TB)) m_override (.row1(b1), .row0(b0), .cnt(cb)); // explicit override -> TB
  mid #(.sel_p(0), .mat_p(TA)) m_override2 (.row1(c1), .row0(c0), .cnt(cc)); // explicit override -> TA
endmodule
