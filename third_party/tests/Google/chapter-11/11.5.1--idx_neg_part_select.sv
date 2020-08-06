/*
:name: idx_neg_part_select
:description: indexed negative part-select bit test
:tags: 11.5.1
*/
module top();
logic [15:0] a;
logic [3:0] b;

initial begin
	b = a[11-:4];
end

endmodule
