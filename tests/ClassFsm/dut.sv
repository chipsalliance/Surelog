module fsm_class (input clk, input reset, input x);

  class baseFsm;
    // properties
    bit [3:0] current_state;
    bit [3:0] next_state;
    // methods
    task next_state_transition (input int state_to_bit);
     // combinatorial
      begin // {
        next_state = 0;
        next_state [state_to_bit] = 1'b1;
      end // }
    endtask
    task current_state_transition (input logic reset);
    // flopped
      begin // {
      if (reset)
        current_state = 0;
      else
        current_state <= next_state;
      end // }
    endtask
  endclass

  class specificFSM extends baseFsm;
    // parameter declaration
    localparam  STATE_00_BIT = 0;
    localparam  STATE_01_BIT = 1;
    localparam  STATE_10_BIT = 2;
    localparam  STATE_11_BIT = 3;
    // methods
    task from_state_00;
      begin // {
      if (x)
        next_state_transition (STATE_01_BIT);
      else
        next_state_transition (STATE_00_BIT);
      end // }
    endtask

    task from_state_01;
      begin // {
        if (~x) 
           next_state_transition (STATE_10_BIT);
        else 
           next_state_transition (STATE_01_BIT);
      end // }
    endtask

    task from_state_10;
      begin // {
        if (x) 
           next_state_transition (STATE_11_BIT);
        else 
           next_state_transition (STATE_10_BIT);
      end // }
    endtask

    task from_state_11;
      begin // {
        if (x)
          next_state_transition (STATE_00_BIT);
        else
          next_state_transition (STATE_11_BIT);
      end // }
     endtask

     task main_comb;
      begin // {
        case (1'b1)
          current_state[STATE_00_BIT]: from_state_00;
          current_state[STATE_01_BIT]: from_state_01;
          current_state[STATE_10_BIT]: from_state_10;
          current_state[STATE_11_BIT]: from_state_11;
        endcase
      end // }
    endtask
  endclass

  specificFSM P;
  always @(posedge clk)begin
    P.current_state_transition(0);
  end 
  always @*
  P.main_comb;
endmodule
