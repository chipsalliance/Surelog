module top(input a, output [2:0] b);
		function automatic logic [2:0] compute_next_state();
		  logic [2:0] function_variable;
		  assign function_variable = 3'b1;
		  return function_variable;
		endfunction : compute_next_state
		assign b = compute_next_state();
		
endmodule
