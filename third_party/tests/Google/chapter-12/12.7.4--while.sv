/*
:name: while_loop
:description: A module testing while loop
:tags: 12.7.4
*/
module while_tb ();
	string test [4] = '{"111", "222", "333", "444"};
	initial begin
		int i = 0;
		while(test[i] != "222")begin
			$display(i, test[i]);
			i++;
		end
	end
endmodule
