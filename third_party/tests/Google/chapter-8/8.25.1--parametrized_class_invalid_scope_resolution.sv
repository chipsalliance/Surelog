/*
:name: parametrized_class_invalid_scope_resolution
:description: parametrized class invalid scope resolution
:should_fail_because: par_cls:: is not permitted in this context
:tags: 8.25.1
:type: simulation
*/
module class_tb ();

	class par_cls #(int a = 25);
		parameter int b = 23;
	endclass

	par_cls #(15) inst;

	initial begin
		inst = new;

		// par_cls:: is not permitted in this context
		$display(par_cls::b);
	end
endmodule
