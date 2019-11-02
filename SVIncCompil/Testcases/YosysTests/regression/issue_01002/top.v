module onehot(i_in, o_out);
	parameter	LG = 7;
	localparam	WID = (1<<LG);
	//
	input	wire	[WID-1:0]	i_in;
	output	reg	[LG-1:0]	o_out;

	//
	integer	N;

	always @(*)
	begin
		o_out = 0;
		for(N=0; N<WID; N=N+1)
		begin
			if (i_in[N])
				o_out = o_out | N[LG-1:0];
		end
	end
endmodule
