/*
:name: event_sequence
:description: sequence event test
:tags: 9.4.2.4
:type: simulation parsing
*/
module seq_tb ();
	wire a = 0;
	wire b = 0;
	wire c = 0;
	wire y = 0;
	wire clk = 0;

	sequence seq;
		@(posedge clk) a ##1 b ##1 c;
	endsequence

	initial begin
		fork
			begin
				@seq y = 1;
				$display(":assert:(True)");
			end
			begin
				a = 1;
				#10 clk = 1;
				#10 clk = 0;
				b = 1;
				#10 clk = 1;
				#10 clk = 0;
				c = 1;
				#10 clk = 1;
				#10 clk = 0;
			end
		join
	end
endmodule
