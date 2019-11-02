module top(clk, en);
	input clk;
	input en;
	reg [3:0] X;
	initial begin
		X = 4'd1;
	end
	always @(posedge clk) begin
		X <= en ? ( (X == 4'd15) ? 4'd1 : (X + 4'd1) ) : X ;
	end
	property1: assert property ( X != 4'd0 );
	property2: assert property ( X > 4'd0 );
endmodule
