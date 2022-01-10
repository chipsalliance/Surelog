`default_nettype wire

module ok;
reg a;
assign b=a;

endmodule

`default_nettype none

module M1(input b);
endmodule

module bad1;
reg a;
assign b=a;

function [1:0] __truncate_to_2_bits(input [1:0] i);
__truncate_to_2_bits = i;
endfunction

endmodule

typedef enum {MODE_A, MODE_B} Mode_t;

typedef enum logic [1:0] {READ=2'd1, WRITE=2'd2, NONE=2'd0} Operation_t;

module bad2;

enum {S_A, S_B, S_C} currentState, nextState;

always_ff @(posedge clock)
if(clear) begin
    currentState <= S_A;
end else begin
    currentState <= nextState;
end

  always_comb begin
        case(mode)
            MODE_A: operation = READ;
            MODE_B: operation = WRITE;
            default: operation = NONE;
        endcase
    end
   
M1 m1(b);

endmodule
