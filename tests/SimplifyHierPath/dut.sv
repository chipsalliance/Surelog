module module_scope_Example(o1);
   parameter [31:0] v1 = 10;
   output wire [31:0] o1;
   assign module_scope_Example.o1 = module_scope_Example.v1;
endmodule

module module_scope_top(
   output wire [31:0] a1
);
   module_scope_Example a(a1);
endmodule

