module  slowfil_fixedtaps(i_clk, i_reset, i_tap_wr, i_tap, i_ce, i_sample, o_ce, o_result);
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
	output	wire	          	o_ce;
	output	wire	[(OW-1):0]	o_result;

	slowfil #(.FIXED_TAPS(1), .NTAPS(NTAPS), .IW(IW), .TW(TW), .INITIAL_COEFFS("taps.hex")) fir (.i_clk(i_clk), .i_reset(i_reset), .i_tap_wr(i_tap_wr), .i_tap(i_tap), .i_ce(i_ce), .i_sample(i_sample), .o_ce(o_ce), .o_result(o_result));
endmodule

`include "slowfil.vh"
