module top
(
 input [1:0] x,
 input [1:0] y,
 input [1:0] z,
 input clk,

 input A,
 output reg B
 );
 
 initial begin
    B = 0;
 end

`ifndef BUG
always @(posedge clk) begin
    if (x || y && z)
        B <=  A & z;
    if (x || y && !z)
        B <=  A | x;
end
`else
always @(posedge clk) begin
    B =  z - y + x;
end
`endif

endmodule
