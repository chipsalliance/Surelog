module signed_shifter (
  input wire [1:0] i,
  output reg signed [3:0] Q );
  integer j;
  always @ * begin
    for(j=0;j<i;j=j+1) Q = 1'b1;
  end
endmodule

