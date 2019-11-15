module top
(
 input signed x,
 input signed y,
 input signed cin,

 output signed A,
 output signed cout,
 output signed B,C
 );


`ifndef BUG
assign A =  y >> x;
assign cout =  y + A >>> y;
assign {B,C} =  {cout,A} << 1;
`else
assign {cout,A} =  cin - y * x;
`endif

endmodule
