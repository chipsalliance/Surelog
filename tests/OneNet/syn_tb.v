module syn_tb(input logic clk, output logic rtl_o, output logic gate_o); 
   logic i;
   
   integer state = 0;

   // Stimulus + Model Checking
   always @ (posedge clk) begin
      if (state==0) begin       
         i <= 0;
	 state <= state+1; 
     end
      else if (state==1) begin
         i <= 1;
         state <= state+1; 	 
	 assert(gate_o == 0) $display("OK!"); else $fatal(1, "o != 0!");
      end
      else if (state==2) begin
         i <= 0;
         state <= state+1;
	 assert(gate_o == 1) $display("OK!"); else $fatal(1, "o != 1!");
      end
      else if (state==3) begin
	 i <= 0;
	 state <= state+1; 
	 assert(gate_o == 0) $display("OK!"); else $fatal(1, "o != 0!");
      end 
      $display("i = %0d, o = %0d", i, gate_o);
   end

   // Miter structure Equivalence checking
   //    
   always @ (posedge clk) begin
     assert(rtl_o == gate_o) $display("OK!"); else $fatal(1, "rtl_o != gate_o");
   end  
   
   dut rtl_model(i,rtl_o);

   synth_dut gate_model(i,gate_o);

endmodule

