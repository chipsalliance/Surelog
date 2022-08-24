`default_nettype none

module module_scope_Example(o1, o2);
   output wire [31:0] o1, o2;
   //assign module_scope_Example.o1 = module_scope_Example.v1;
   //assign module_scope_Example.o2 = module_scope_Example.v2;
   assign module_scope_Example.o2 = v2;
endmodule
