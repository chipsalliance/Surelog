module syn_tb(fsm1clk, fsm2clk, fsm3clk, fsm1rst, SlowRam, fsm2rst,  ctrl, keys, brake, accelerate, gate_rd, gate_wr, gate_Fsm2Out, gate_speed); 
   
input fsm1clk, fsm2clk, fsm3clk, fsm1rst, SlowRam;

input  fsm2rst, ctrl;
input  keys, brake, accelerate;
output [3:0] gate_speed;   
output [2:0] gate_Fsm2Out;
output gate_rd, gate_wr;  
      
wire fsm1clk, fsm3clk, fsm1rst, SlowRam, fsm2rst;
wire ctrl;
wire keys, brake, accelerate;

wire rtl_rd, rtl_wr, gate_rd, gate_wr;   
wire [3:0] rtl_speed;
wire [3:0] gate_speed;
wire [2:0] rtl_Fsm2Out;
wire [2:0] gate_Fsm2Out;
   
   // Miter structure Equivalence checking
   //    
   always @ (posedge fsm1clk) begin
     assert(rtl_rd == gate_rd) $display("OK!"); else $fatal(1, "rtl_rd != gate_rd");
     assert(rtl_wr == gate_wr) $display("OK!"); else $fatal(1, "rtl_wr != gate_wr");
   end 
    
   
   dut rtl_model(fsm1clk, fsm2clk, fsm3clk, fsm1rst, SlowRam, fsm2rst,  ctrl, keys, brake, accelerate, rtl_rd, rtl_wr, rtl_Fsm2Out, rtl_speed);

   synth_dut gate_model(fsm1clk, fsm2clk, fsm3clk, fsm1rst, SlowRam, fsm2rst,  ctrl, keys, brake, accelerate, gate_rd, gate_wr, gate_Fsm2Out, gate_speed);

endmodule

