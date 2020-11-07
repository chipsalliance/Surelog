module fsm_using_function (
input bit clock , // clock
input bit reset , // Active high, syn reset
input bit req_0 , // Request 0
input bit req_1 , // Request 1
output bit gnt_0 , // Grant 0
output bit gnt_1 // Grant 1
);

//-------------STATE VARIABLES--------------------------
typedef enum logic [1:0] {IDLE = 1,GNT0 = 2,GNT1 = 3} state;
state curr_state, next_state;
//----------Code startes Here------------------------

always @ (posedge clock)
begin : FUN
 assign next_state = fsm_function(curr_state, req_0, req_1, next_state);
end

//----------Function for Combo Logic-----------------
function fsm_function(input logic [1:0] state, input bit req_0,input bit req_1, output logic [1:0] future_state);
case(state)
  IDLE : if (req_0 == 1'b1) begin
           future_state = GNT0; 
         end else if (req_1 == 1'b1) begin 
           future_state= GNT1; 
         end else begin
           future_state = IDLE; 
         end
  GNT0 : if (req_0 == 1'b1) begin
           future_state = GNT0;
         end else begin
           future_state = IDLE;
         end
  GNT1 : if (req_1 == 1'b1) begin
           future_state = GNT1;
         end else begin
           future_state = IDLE; 
         end
  default : future_state = IDLE; 
endcase
endfunction

//----------Sequential Logic-----------------------------
always @ (posedge clock)
begin : FSM_SEQ
 if (reset == 1'b1) begin
    curr_state <= #1 IDLE;
 end else begin
    curr_state <= #1 next_state;
 end
end
endmodule // End of Module arbiter
