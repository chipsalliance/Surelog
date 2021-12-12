module top(output logic [31:0] o);
   typedef struct packed {
      logic x;
   } [31:0] struct_array_t;
   struct_array_t a = '1;
   assign o = a;
endmodule
