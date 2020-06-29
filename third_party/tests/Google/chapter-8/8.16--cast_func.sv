/*
:name: cast_func
:description: $cast function test
:tags: 8.16
*/
module class_tb ();
	typedef enum { aaa, bbb, ccc, ddd, eee } values;
	initial begin
		values val;
		if(!$cast(val, 5))
			$display("$cast failed");
		$display(val);
	end
endmodule
