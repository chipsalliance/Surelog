/*
:name: delay_control
:description: delay control
:tags: 9.4.1
*/
module block_tb ();
	reg [3:0] a = 0;
	initial begin
		#10 a = 'h1;
		#10 a = 'h2;
		#10 a = 'h3;
		#10 a = 'h4;
	end
endmodule
