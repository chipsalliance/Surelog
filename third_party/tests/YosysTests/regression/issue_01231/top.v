module	fnmcve(o_crc);
	output	reg	[7:0]	o_crc;

	always @(*)
		o_crc = gencrc({ 2'b01, 6'h11, 32'h00 });

	function [7:0]	gencrc;
		input	[39:0]	i_cmdword;
		integer	icrc;

		gencrc = 0;
		for(icrc=0; icrc<40; icrc=icrc+1)
		if (i_cmdword[39-icrc] ^ gencrc[7])
			gencrc[7:1] = { gencrc[6:1], 1'b0 } ^ 7'h09;
		else
			gencrc[7:1] = { gencrc[6:1], 1'b0 };
		gencrc = { gencrc[7:1], 1'b1 };
	endfunction
endmodule
