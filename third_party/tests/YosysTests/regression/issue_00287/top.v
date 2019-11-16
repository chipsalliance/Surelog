module top(input [6:0] D, input [1:0] S, output reg [1:0] Y);
  always @* begin : block
    reg [3:0] data [0:3];
    data[0] = D[3:0];
    data[1] = D[4:1];
    data[2] = D[5:2];
    data[3] = D[6:3];
    Y = data[S];
  end
endmodule
