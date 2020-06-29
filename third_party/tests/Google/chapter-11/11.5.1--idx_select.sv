/*
:name: idx_select
:description: indexed select bit test
:tags: 11.5.1
*/
module top();
logic [15:0] a;
logic b;

initial begin
	b = a[11];
end

endmodule
