////////////////////////////////////////////////////////////////////////////////
//
////////////////////////////////////////////////////////////////////////////////
//
`default_nettype	none
//
module	mcvesix(i_clk, i_bits, o_char);
	input	wire		i_clk;
	input	wire	[6:0]	i_bits;
	output	reg	[7:0]	o_char;

	reg	[6:0]	remap	[0:127];

	integer	k, newv;
	always @(*) begin
		for(k=0; k<128; k=k+1)
		begin
			newv = 0;
// `define	BROKEN_CODE
`ifdef	BROKEN_CODE
			if (k[6])
`else
			if (k >= 64)
`endif
				newv = 7'h0a;
			else
				newv = k;

			remap[k] = newv;
		end
	end

	initial	o_char = 8'h00;
	always @(posedge i_clk)
		o_char <= { 1'b0, remap[i_bits] };

`ifdef	FORMAL
	reg	[7:0]	f_char;

	//
	// Here's the old encoding that "worked"
	//
	initial	f_char = 8'h00;
	always @(posedge i_clk)
	begin
		if (i_bits[6])
			f_char <= 8'h0a;
		else
			f_char <= i_bits[6:0];
	end

	//
	// Now let's prove that the two encodings are equivalent
	always @(*)
		assert(f_char == o_char);
`endif
endmodule

