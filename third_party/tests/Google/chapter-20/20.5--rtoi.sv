/*
:name: rtoi_function
:description: $rtoi test
:tags: 20.5
:type: simulation parsing
*/

module top();

initial begin
	$display(":assert: (%d == 21)", $rtoi(21.37));
end

endmodule
