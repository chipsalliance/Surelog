module top_veri_v2k #(parameter WIDTH=1, INIT=1, greeting="hello") (input clk, input [WIDTH-1:0] i, output reg o);
initial begin 
	o <= INIT;
	$display("%s", greeting);
end
always @(posedge clk)
	o <= ^i;
endmodule

module top_veri_95(clk, i, o);
parameter WIDTH=1;
parameter INIT=1;
parameter greeting="hello";
input clk;
input [WIDTH-1:0] i;
output o;
reg o;
initial begin 
	o <= INIT;
	$display("%s", greeting);
end
always @(posedge clk)
	o <= ^i;
endmodule
