module top
(
 input x,
 input y,
 input z,
 input clk,

 input A,
 output B
 );
 
`ifndef BUG
assign  B = (x || y || !z)?  (A & z) : ~x;
`else
assign B =  z - y + x;

`endif

endmodule
