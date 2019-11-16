module inivalue(i_clk, i_val, o_val);
	input	wire	i_clk;
	input	wire	[2:0]	i_val;
	output	reg	[1:0]	o_val;

	reg	[2:0]	r_val;

	initial	r_val = 0;
	always @(posedge i_clk)
		r_val <= r_val + i_val;

	always @(*)
		o_val = r_val[1:0];

endmodule
