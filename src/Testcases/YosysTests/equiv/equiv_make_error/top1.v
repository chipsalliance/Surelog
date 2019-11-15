module top(input wire clk,output reg count);

always @(posedge clk)begin
	count <= count + 1'b1;
end

endmodule
