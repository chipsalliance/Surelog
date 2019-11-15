`timescale 1 ms / 1 ps
module test;
    initial begin
	// NOTE: These delays, when scaled to sim time,
	// overflow 32bit deltas and cause vvp to fail.
	#12345.6789;
	$display("time = %0f", $time);
	$test(test);
	#2345.67891;
	$display("time = %0f", $time);
	$test(test);
    end
endmodule

`timescale 1 ps / 1 ps
module test2;
    initial begin
	#12345.6789;
	$display("time = %0f", $time);
	$test(test2);
	#2345.67891;
	$display("time = %0f", $time);
	$test(test2);
    end
endmodule
