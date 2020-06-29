/*
:name: display_boh
:description: $display test
:tags: 21.2
:type: simulation parsing
*/
module top();

initial begin
	int val = 1234;
	$displayb(val);
	$displayo(val);
	$displayh(val);
end

endmodule
