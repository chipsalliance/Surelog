/*
:name: write_boh
:description: $write test
:tags: 21.2
:type: simulation parsing
*/
module top();

initial begin
	int val = 1234;
	$writeb(val);
	$writeo(val);
	$writeh(val);
end

endmodule
