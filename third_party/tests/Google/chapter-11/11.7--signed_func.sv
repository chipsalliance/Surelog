/*
:name: signed_func
:description: $signed() test
:tags: 11.7
*/
module top();

logic signed [7:0] a;

initial begin
	a = $signed(4'b1000);
end

endmodule
