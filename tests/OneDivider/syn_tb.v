module syn_tb(input logic rstn,
              input logic clk, 
              output logic rtl_div,  
              output logic gate_div); 

   // Miter structure
   //    
   always @ (posedge clk) begin
     assert(rtl_div == gate_div) $display("OK!"); else $fatal(1, "rtl_div != gate_div");
   end
   
   dut rtl_model(rstn, clk, rtl_div);

   synth_dut gate_model(rstn, clk, gate_div);
 
endmodule
