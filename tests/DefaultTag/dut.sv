module top();
   typedef struct packed {
      logic [1:0] a;
      logic [2:0] b;
      logic [2:0] c;
      logic [2:0] d;
   } struct_1;
   parameter struct_1 X = '{b: 10, d: 20, default: 15};
endmodule

