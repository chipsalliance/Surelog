module top
(
 input x,
 input y,
 input cin,

 output A,
 output cout
 );

`ifndef BUG
assign cout = x / y * cin;
`else
assign {cout,A} =  cin - y * x;
`endif

endmodule
