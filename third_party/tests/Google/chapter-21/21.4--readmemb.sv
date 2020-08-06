/*
:name: readmemb_task
:description: $readmemb test
:tags: 21.4
:type: parsing
*/
module top();

logic [31:0] mem0 [1023:0];
string fname0 = "test0.mem";

initial begin
	$readmemb(fname0, mem0);
end

endmodule
