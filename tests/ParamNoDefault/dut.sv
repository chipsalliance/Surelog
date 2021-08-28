module dut();
   parameter logic [4:0] A;
 
endmodule // dut

module top();
   typedef struct packed {
      logic [1:0] a;
   
   } struct_1;

 
      
   parameter struct_1 X = '{a: '1, b: '0};
   

   dut #(.A(X)) u_dut();
endmodule
