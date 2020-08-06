module top();

	localparam int unsigned NrHarts2 = 8;
 
	localparam int unsigned HartSelLen1 = (NrHarts == 1) ? 1 : $clog2(NrHarts);
	
	localparam int unsigned HartSelLen2 = (NrHarts == 1) ? 1 : 0;

	localparam int unsigned HartSelLen3 = (NrHarts == 1) ? 1 : $clog2(NrHarts2);

endmodule
