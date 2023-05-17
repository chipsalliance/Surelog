package my_package;
typedef logic [1:0] typedef_logic_typespec;
endpackage: my_package

module logic_typespec ();

my_package::typedef_logic_typespec    [1:0][7:0] my_instance;

endmodule : logic_typespec
