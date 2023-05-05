module top (out);
  output wire [31:0] out;

  assign out = $unsigned({(~^$unsigned((~&(8'ha4))))});
endmodule
