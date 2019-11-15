module  fastfir_dynamictaps(i_clk, i_reset, i_tap_wr, i_tap, i_ce, i_sample, o_result);
`ifdef	FORMAL
	parameter		NTAPS=16, IW=9, TW=IW, OW=2*IW+5;
`else
	parameter		NTAPS=128, IW=12, TW=IW, OW=2*IW+7;
`endif
	parameter [0:0]		FIXED_TAPS=0;
	input	wire			i_clk, i_reset;
	//
	input	wire			i_tap_wr;	// Ignored if FIXED_TAPS
	input	wire	[(TW-1):0]	i_tap;		// Ignored if FIXED_TAPS
	//
	input	wire			i_ce;
	input	wire	[(IW-1):0]	i_sample;
	output	wire	[(OW-1):0]	o_result;

	fastfir #(.FIXED_TAPS(0), .NTAPS(NTAPS), .IW(IW), .TW(TW)) fir (.i_clk(i_clk), .i_reset(i_reset), .i_tap_wr(i_tap_wr), .i_tap(i_tap), .i_ce(i_ce), .i_sample(i_sample), .o_result(o_result));
endmodule

`include "fastfir.vh"
`include "firtap.vh"
