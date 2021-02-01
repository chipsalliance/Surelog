package my_funcs;
   
   function automatic int simple_minus (input int value1, input int value2);
      begin
	      simple_minus = value1 - value2;
      end
   endfunction

   function automatic int simple_func (input int value1, input int value2);
      begin
	      simple_func = simple_minus(.value2(value2), .value1(value1));
      end
   endfunction
endpackage

package my_module_types;
   import my_funcs::*;

   localparam MY_PARAM = 3;
   localparam MY_PARAM2 = simple_func(.value2(12), .value1(24));
endpackage

module t
  import my_module_types::*;
   (
    input 			i_clk,
    input [MY_PARAM-1:0] 	i_d,
    output logic [MY_PARAM-1:0] o_q
    );

endmodule
