/*
:name: foreach_loop
:description: A module testing foreach loop
:tags: 12.7.3
*/
module foreach_tb ();
	string test [4] = '{"111", "222", "333", "444"};
	initial begin
		foreach(test[i])
			$display(i, test[i]);
	end
endmodule
