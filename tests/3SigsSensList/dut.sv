module dut (

input wire							clk,
input wire							rst,
input wire	start
);

/*
Yosys requires the following template:
 
wire \synlig_tmp = rst | start;
always @ (posedge clk or posedge \synlig_tmp ) 
begin
    if (\synlig_tmp ) begin
		outputLine <= 0;		
	end
	else
	begin
		yScaleAmountNext <= 0;
	end
end
*/

always @ (posedge clk or posedge rst or posedge start)
begin
	if(rst | start)
	begin
	  outputLine <= 0;	
	end
	else
	begin	
	 yScaleAmountNext <= 0;
	end
end

endmodule
