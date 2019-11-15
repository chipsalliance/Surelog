module top(input wire clk,rst,output reg count);

always @(posedge clk or posedge rst)begin
	if(rst)
		count <= 0;
	else
		count <= count + 1'b1;
end

endmodule
