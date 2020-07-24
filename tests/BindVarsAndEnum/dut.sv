module conditional_Fsm ( input bit reset,
  input bit increment,
  output int count );
  
  bit clock;
  
  typedef enum logic [1:0] {RESET, COUNTER, COUNTER_DONE} state;
  state curr_state, next_state;
  
  //Clock Generation Logic
  always #10ns clock = ~clock;
  
  always_ff @(posedge clock) begin
  if (reset) begin
  curr_state <= RESET;   
  end
end
endmodule // conditional_Fsm

