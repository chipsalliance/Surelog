module vend(clock, newspaper);
//Input output port declarations
input clock;
output newspaper;
wire newspaper;
//state encodings
parameter s0 = 2'b00;

//Combinational logic
function [2:0] fsm;
input [1:0] fsm_PRES_STATE;
reg fsm_newspaper;

begin
    case (fsm_PRES_STATE)   
    s0: //state = s0
    begin
        if (fsm_coin == 2'b10)
            begin
                fsm_newspaper = 1'b0;  
            end   
    end        
    endcase
fsm = fsm_newspaper;
end
endfunction

always @(posedge clock)
begin
  assign newspaper = fsm(PRES_STATE);
end

endmodule
