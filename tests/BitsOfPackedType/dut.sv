module dut (
  input  logic [7:0]  a,
  output logic [31:0] w,
  output logic [$bits(logic [15:0])-1:0] p,
  output logic [7:0]  q
);
  localparam int W1 = $bits(logic [31:0]);
  localparam int W2 = $bits(logic);
  localparam int W3 = $bits(logic [3:0][7:0]);
  typedef logic [31:0] t32;
  localparam int W4 = $bits(t32);
  localparam int W5 = $bits(bit [1:0][2:0][3:0]);
  assign w = {W1[7:0], W2[7:0], W3[7:0], W4[7:0]} ^ {4{a}};
  assign p = {2{a}};
  assign q = W5[7:0] + a;
endmodule
