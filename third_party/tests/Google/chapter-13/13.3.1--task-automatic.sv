/*
:name: task_automatic
:description: automatic task test
:tags: 13.3.1
:type: simulation parsing
*/
module top();

task automatic mytask;
	int a = 0;
	a++;
	$display(":assert:(%d == 1)", a);
endtask

initial begin
   mytask;
   mytask;
   mytask;
   mytask;
end

endmodule
