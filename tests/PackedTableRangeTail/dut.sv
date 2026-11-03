package ptv_pkg;
  parameter logic [3:0][15:0] RC = {16'h0123, 16'hfedc, 16'h1111, 16'h2222};
endpackage
module top (input logic [7:0] d_i, output logic [7:0] b_o, output logic [15:0] c_o, output logic [3:0] e_o);
  // a select path with a RANGE tail on a flat package table: must not be folded as a chain of element indices
  assign b_o = {ptv_pkg::RC[3][8 +: 4], ptv_pkg::RC[1][15], ptv_pkg::RC[1][0], ptv_pkg::RC[0][15 -: 2]};
  assign c_o = ptv_pkg::RC[2][15:0] ^ {8'h0, d_i};
  assign e_o = ptv_pkg::RC[0][3:0];
endmodule
