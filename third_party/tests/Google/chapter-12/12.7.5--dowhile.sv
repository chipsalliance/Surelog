/*
:name: dowhile_loop
:description: A module testing do..while loop
:tags: 12.7.5
*/
module dowhile_tb ();
	string test [4] = '{"111", "222", "333", "444"};
	initial begin
		int i = 0;
		do begin
			$display(i, test[i]);
			i++;
		end while(test[i] != "222"); 
	   
	end
endmodule
