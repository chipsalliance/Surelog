module top
(
	input [7:0] data_a, data_b,
	input [6:1] addr_a, addr_b,
	input we_a, we_b, re_a, re_b, clka, clkb,
	output reg [7:0] q_a, q_b
);
	// Declare the RAM variable
	reg [7:0] ram[63:0];
	
	initial begin
        q_a <= 8'h00;        
        q_b <= 8'd0;
	end
	
	// Port A
	always @ (posedge clka)
	begin
`ifndef BUG        
		if (we_a) 
`else        
		if (we_b) 
`endif
		begin
			ram[addr_a] <= data_a;
			q_a <= data_a;
		end
		if (re_b) 
		begin
			q_a <= ram[addr_a];
		end
	end
	
	// Port B
	always @ (posedge clkb)
	begin
`ifndef BUG        
		if (we_b) 
`else        
		if (we_a) 
`endif
		begin
			ram[addr_b] <= data_b;
			q_b <= data_b;
		end
		if (re_b)
		begin
			q_b <= ram[addr_b];
		end
	end
	
endmodule								 
