/*
 * This test verifies vpiPureTransportDelay functionality
 */

`timescale 1 ns / 1 ps
module test;
    reg r;
    initial begin
	$monitor("<monitor> r = ", r);
	r = 1'b0;
	#100000 $finish;
    end
    always @(r) $display("<display> r = %b @ %0t", r, $time);

endmodule
