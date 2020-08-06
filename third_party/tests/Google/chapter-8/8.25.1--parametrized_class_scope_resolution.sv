/*
:name: parametrized_class_scope_resolution
:description: parametrized class scope resolution
:tags: 8.25.1
*/
module class_tb ();

	class par_cls #(int a = 25);
		parameter int b = 23;
	endclass

	par_cls #(15) inst;

	initial begin
		inst = new;

		$display(par_cls#()::b);
	end
endmodule
