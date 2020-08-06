/*
:name: function_static
:description: static function test
:tags: 13.4.2
*/
module top();

function static int add(int val);
	int a = 0;
	a = a + val;
	return a;
endfunction

initial
	begin
		$display(":assert: (%d == 5)", add(5));
		$display(":assert: (%d == 10)", add(5));
		$display(":assert: (%d == 15)", add(5));
		$display(":assert: (%d == 20)", add(5));
	end

endmodule
