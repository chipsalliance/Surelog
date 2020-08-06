/*
:name: sscanf_task
:description: $sscanf test
:tags: 21.3
:type: simulation parsing
*/
module top();

string str = "1234";
int c;

initial begin
	$sscanf(str, "%d", c);
	$display(":assert: (%d == %s)", c, str);
end

endmodule
