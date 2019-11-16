module top
(
 input x,
 input y,
 input z,
 input clk,

 input A,
 output signed B,
 output signed C,D,E
 );
 
`ifndef BUG
assign  B = (x || y || !z)?  (A & z) : ~x;
assign {D,C} =  {y,z} >>> 1;
assign E = {x,y,z} / 3;
`else
assign B =  z - y + x;

`endif

endmodule
