module top (
		 input clkIn,
		 output clkOut
		 );


 // Set up clock for 48Mhz with input of 12MHz
   SB_PLL40_CORE #(
		   .FEEDBACK_PATH("SIMPLE"),
		   .PLLOUT_SELECT("GENCLK"),
		   .DIVR(4'b0000),
		   .DIVF(7'b0111111),
		   .DIVQ(3'b100),
		   .FILTER_RANGE(3'b001)
		   ) uut (
			  .LOCK(lock),
			  .RESETB(1'b1),
			  .BYPASS(1'b0),
			  .REFERENCECLK(clkIn),
			  .PLLOUTCORE(clkOut)
			  );
endmodule
