module top
(
 input x,
 input y,
 input cin,

 output A,
 output cout
 );

`ifndef BUG
 wire pow,p,n;

assign pow = 2 ** y;

assign p =  +x;
assign n =  -x;
assign A =  cin * x;
`else
assign {cout,A} =  cin - y * x;
`endif

endmodule
