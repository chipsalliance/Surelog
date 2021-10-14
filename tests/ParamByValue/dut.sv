package lc_ctrl_state_pkg;
  parameter logic [15:0] B0 = 16'b1110011001111001; 
  parameter logic [15:0] B1 = 16'b1101111101101110;
  typedef enum logic [31:0] {
    LcStScrap         = {B1,  B0}
  } lc_state_e;               
endpackage 

module generic_flop #(parameter logic [15:0] ResetValue = 0) ( );                
endmodule  

module prim_flop #( parameter logic [15:0] ResetValue = 0) ();                                        
    //import lc_ctrl_state_pkg::*;
    generic_flop #(   
      .ResetValue(ResetValue)      
    ) impl_generic ();                                                                             

endmodule

module top();
  import lc_ctrl_state_pkg::*; 
 
  prim_flop #(
    .ResetValue(32'(LcStScrap))
  ) state_regs ();

endmodule 
