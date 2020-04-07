module syn_tb(input logic clk, output logic rtl_o, output logic gate_o); 
   logic a, b;
   
   integer state = 0;

   // Stimulus + Model Checking
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
         $display("%0d & %0d = %0d", a, b, gate_o);
	 assert(gate_o == (a & b)) $display("OK!"); else $fatal(1, "o != (a & b)!");
      end
      else if (state==2) begin
         a <= 1;
         b <= 0;
         state <= state+1;
         $display("%0d & %0d = %0d", a, b, gate_o);
	 assert(gate_o == (a & b)) $display("OK!"); else $fatal(1, "o != (a & b)!");
      end
      else if (state==3) begin
	 a <= 0;
	 b <= 1;
	 state <= state+1; 
	 $display("%0d & %0d = %0d", a, b, gate_o);
	 assert(gate_o == (a & b)) $display("OK!"); else $fatal(1, "o != (a & b)!");
      end 
      else if (state==4) begin
	 $display("%0d & %0d = %0d", a, b, gate_o);
	 assert(gate_o == (a & b)) $display("OK!"); else $fatal(1, "o != (a & b)!");
	 state <= state+1; 
	 $finish; 
      end 
   end

   // Miter structure Equivalence checking
   //    
   always @ (posedge clk) begin
     assert(rtl_o == gate_o) $display("OK!"); else $fatal(1, "rtl_o != gate_o");
   end  
   
   dut rtl_model(a,b,rtl_o);

   synth_dut gate_model(a,b,gate_o);

endmodule

