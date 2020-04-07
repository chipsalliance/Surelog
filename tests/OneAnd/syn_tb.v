module syn_tb(input logic clk, output logic o); 
   logic a, b;
   
   integer state = 0;

   always @ (posedge clk) begin
      if (state==0) begin       
         a <= 0;
         b <= 0;
	 state <= state+1; 
     end
      else if (state==1) begin
         a <= 1;
         b <= 1;
         state <= state+1; 	 
         $display("%0d & %0d = %0d", a, b, o);
      end
      else if (state==2) begin
         a <= 1;
         b <= 0;
         state <= state+1; 
         $display("%0d & %0d = %0d", a, b, o);
      end
      else if (state==3) begin
	 a <= 0;
	 b <= 1;
	 state <= state+1; 
	 $display("%0d & %0d = %0d", a, b, o);
      end 
      else if (state==4) begin
	 $display("%0d & %0d = %0d", a, b, o);
	 state <= state+1; 
	 $finish; 
      end 
   end
   
   dut dut1(a,b,o);
    
endmodule
