
  module fsm_2_always_block ;

    always @(posedge clk or negedge rst_n) begin
    
    if (!rst_n) 
      state <= IDLE;
    else 
      stateAsmt(state,next);
      
    end
    
    function stateAsmt(reg [1:0] curr_state,next_state) ;
         curr_state = next_state;
    endfunction
    
    
    endmodule 