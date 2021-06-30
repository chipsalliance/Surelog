package pkg;
   typedef struct packed {
      logic 	  x;
   } a;
   typedef a b[5:0];
endpackage
   
module dut(output o);
   pkg::b c;
   assign c[1].x = 1;
   assign o = c[1].x;   
endmodule   
