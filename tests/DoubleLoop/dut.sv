
module constpower1(ys, yu);

output [2:0] ys, yu;

genvar i, j;

generate
	for (i = 0; i < 2; i = i+1) 
	for (j = 0; j < 2; j = j+1) begin:W
		assign ys= i + j;
		
	end

endgenerate

endmodule

module constpower2(ys, yu);

output [2:0] ys, yu;

genvar i, j;

generate
	for (i = 0; i < 2; i = i+1) 
	for (j = 0; j < 2; j = j+1) begin
		assign ys= i + j;
		
	end

endgenerate

endmodule

module constpower3(ys, yu);

output [2:0] ys, yu;

genvar i, j;

generate
	for (i = 0; i < 2; i = i+1) begin
	for (j = 0; j < 2; j = j+1) 
		assign ys= i + j;
		
	end

endgenerate

endmodule // constpower3

module constpower4(ys, yu);

output [2:0] ys, yu;

genvar i, j;

generate
	for (i = 0; i < 2; i = i+1) begin
	for (j = 0; j < 2; j = j+1) begin
		assign ys= i + j;
		
	end
        end

endgenerate

endmodule // constpower4


module constpower5(ys, yu);

output [2:0] ys, yu;

genvar i, j;

generate
	for (i = 0; i < 2; i = i+1) 
	for (j = 0; j < 2; j = j+1) 
		assign ys= i + j;
		
	
        

endgenerate

endmodule // constpower5
