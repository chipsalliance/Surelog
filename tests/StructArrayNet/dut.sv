package pkg;
  parameter int N=32;
   typedef struct packed { logic x; } Struct;
endpackage

module mod(input pkg::Struct struct_i);
endmodule;

module dut(input int sel);
   pkg::Struct [pkg::N-1:0]    struct_array;
   
   mod m(.struct_i(struct_array[sel]));
endmodule
