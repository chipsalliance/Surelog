module fsm_2_always_block ();


function stateAsmt(reg [1:0] curr_state,next_state) ;
     curr_state = next_state;
endfunction

endmodule // fsm_2_always_block
