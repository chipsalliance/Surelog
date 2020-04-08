module syn_tb(input logic rstn,
              input logic clk, 
              output logic rtl_q,  
              output logic gate_q); 

  logic d;
  integer state = 0;

  // Stimulus + Model Checking
   always @ (posedge clk) begin
      if (state==0) begin       
         d <= 0;
	 state <= state+1; 
     end
      else if (state==1) begin
         d <= 1;
         state <= state+1; 	 
	 assert(gate_q == 0) $display("OK!"); else $fatal(1, "d != 0!");
      end
      else if (state==2) begin
         d <= 1;
         state <= state+1;
	 assert(gate_q == 0) $display("OK!"); else $fatal(1, "d != 0!");
      end
      else if (state==3) begin
	 d <= 0;
	 state <= state+1; 
	 assert(gate_q == 1) $display("OK!"); else $fatal(1, "d != 1!");
      end 
      else if (state==4) begin
	 d <= 0;
	 state <= state+1; 
	 assert(gate_q == 1) $display("OK!"); else $fatal(1, "d != 1!");
      end
      else if (state==5) begin
	 d <= 1;
	 state <= state+1; 
	 assert(gate_q == 0) $display("OK!"); else $fatal(1, "d != 0!");
      end
      else if (state==6) begin
	 d <= 0;
	 state <= state+1; 
	 assert(gate_q == 0) $display("OK!"); else $fatal(1, "d != 0!");
      end
      else if (state==7) begin
	 d <= 0;
	 state <= state+1; 
	 assert(gate_q == 1) $display("OK!"); else $fatal(1, "d != 1!");
      end
      else if (state==8) begin
	 d <= 0;
	 state <= state+1; 
	 assert(gate_q == 0) $display("OK!"); else $fatal(1, "d != 0!");
      end  
      $display("d = %0d, q = %0d", d, gate_q);

   end



   
   // Miter structure
   //    
   always @ (posedge clk) begin
     assert(rtl_q == gate_q) $display("OK!"); else $fatal(1, "rtl_q != gate_q");
   end
   
   dut rtl_model(d, rstn, clk, rtl_q);

   synth_dut gate_model(d, rstn, clk, gate_q);
 
endmodule
