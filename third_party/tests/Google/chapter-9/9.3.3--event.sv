/*
:name: event_order
:description: event order test
:tags: 9.3.3
*/
module block_tb ();
	event ev;
	reg [3:0] a = 0;
	initial fork
		begin
			a = 'h3;
			#20;
			->ev;
		end
		begin
			@ev
			a = 'h4;
		end
	join
endmodule
