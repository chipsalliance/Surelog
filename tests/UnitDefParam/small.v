
module secret_number;
 parameter SIZE = 0;
   
   genvar i; 
 generate for (i=0; i<SIZE; i=i+1) begin :B1
  M1 N1();
 end

 endgenerate
     	 
endmodule
    
module defparam_example();
  defparam defparam_example.U1.SIZE = 1; 	 
  defparam U2.SIZE = 2;
  defparam U3.SIZE = 3;
  defparam U3.SIZE = 3;
  secret_number U0();  	 
  secret_number U1();
  secret_number U2();
  secret_number U3();  
  NO_DEF U5();
  defparam U5.SIZE = 1;
  defparam NO_MATCH.SIZE1 = 2; 
  defparam defparam_example.NO_MATCH.SIZE2 = 2; 
endmodule

