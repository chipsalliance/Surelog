module top
(
 input x,
 input [1:0] y,
 input z,

 output [1:0] A,
 output [2:0] B,
 output [3:0] C
 );


`ifndef BUG
assign A =  {x,z};
assign B = {x,y};
assign C =  {x,y,z};
`else
assign A =  x + z;
assign B = x * y;
assign C =  x - y - z;
`endif

endmodule


module test(input [7:0] A, B, output [7:0] Y);
  wire [15:0] AB = (A * B) + {A, B};  // merging to create {A, B}
  assign Y = AB[15:8] + AB[7:0];      // splitting to create AB[15:8] and AB[7:0]
endmodule
