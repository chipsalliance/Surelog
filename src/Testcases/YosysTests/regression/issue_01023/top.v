module mux_case_5_1(i, s, o);
  input [4:0] i;
  output o;
  input [2:0] s;
  \$shiftx  #(
    .A_SIGNED(32'd0),
    .A_WIDTH(32'd1),
    .B_SIGNED(32'd0),
    .B_WIDTH(32'sd0),
    .Y_WIDTH(32'd1)
  ) _34_ (
    .A(i[4]),
    .B(),
    .Y(o)
  );
endmodule
