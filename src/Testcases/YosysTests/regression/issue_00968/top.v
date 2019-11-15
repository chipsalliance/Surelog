module mcve1(i_value, o_value);
	input	wire	[3:0]	i_value;
	output	reg	[7:0]	o_value;

	integer k;
	always @(*)
	begin
		for(k=0; k<4; k=k+1)
			o_value[k] = i_value[k];
		o_value[4] = i_value[k];
		o_value[5] = i_value[k];
		o_value[6] = i_value[k];
		o_value[7] = i_value[k];
	end
endmodule
