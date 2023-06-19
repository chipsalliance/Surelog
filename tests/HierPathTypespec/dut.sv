package pkg;
   typedef struct packed {
      logic       x;
   } a;
   typedef a[5:0] b;
endpackage
   
module top(output o);

   pkg::b c;
  
   assign c[1].x = 1;
   assign o = c[1].x;   
endmodule
