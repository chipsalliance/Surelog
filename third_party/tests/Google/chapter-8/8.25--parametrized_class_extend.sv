/*
:name: parametrized_class_extend
:description: parametrized class extending another parametrized class
:tags: 8.25
*/
module class_tb ();
	class base_cls #(int b = 20);
		int a;
	endclass

	class ext_cls #(int e = 25) extends base_cls #(5);
		int c;
	endclass

	ext_cls #(15) inst;

	initial begin
		inst = new;
	end
endmodule
