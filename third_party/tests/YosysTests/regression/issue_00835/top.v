`default_nettype	none
//
module mcve(i_clk, i_stb, o_full);
	parameter	NS = 4;
	parameter	LGCOUNT = 10;
	input	wire		i_clk;
	input	wire	[NS-1:0]	i_stb;
	output	wire	[NS-1:0]	o_full;

	reg	[LGCOUNT-1:0]	counters [0:NS-1];

	genvar	N;
	generate for(N=0; N<NS; N=N+1)
	begin

		initial	counters[N] = 0;
		always @(posedge i_clk)
		if (i_stb[N] && (~counters[N] != 0))
			counters[N] <= counters[N]+1;

		assign	o_full[N] = (&counters[N]);

	end endgenerate

`ifdef	FORMAL
	generate for(N=0; N<NS; N=N+1)
	begin
		always @(*)
		assert(o_full[N] == (&counters[N]));
	end endgenerate
`endif
endmodule
