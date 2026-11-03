package pkg;
  // one FLAT concatenation for a three-dimensional table, non-zero-based ranges
  localparam logic [2:1][1:0][3:2][7:0] LUT = {8'd1, 8'd2, 8'd3, 8'd4, 8'd5, 8'd6, 8'd7, 8'd8};
  localparam logic [1:0][1:0][15:0]     T2  = {16'd3, 16'd5, 16'd6, 16'd7};
endpackage
module top (input logic [7:0] a, output logic [7:0] y, output logic [15:0] z);
  localparam int unsigned N = 32'(pkg::LUT[2][1][3]);   // first element: 1
  localparam int unsigned M = 32'(pkg::LUT[1][0][2]);   // last element: 8
  localparam int unsigned K = pkg::T2[1][0];            // 5
  for (genvar k = 0; unsigned'(k) < N; k++) begin : g_n
    assign y[k] = ~a[k];
  end
  for (genvar k = N; unsigned'(k) < M; k++) begin : g_m
    assign y[k] = a[k];
  end
  assign z = K;
endmodule
