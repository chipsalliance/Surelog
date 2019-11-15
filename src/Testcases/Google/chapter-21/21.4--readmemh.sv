/*
:name: readmemh_task
:description: $readmemh test
:should_fail: 0
:tags: 21.4
:type: parsing
*/
module top();

logic [31:0] mem1 [1023:0];
string fname1 = "test1.mem";

initial begin
	$readmemh(fname1, mem1);
end

endmodule
