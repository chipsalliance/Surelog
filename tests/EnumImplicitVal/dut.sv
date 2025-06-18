typedef enum logic [1:0] {
    A = 3, B = 0, C, D
} state_t;
/*
module top(input clk, output z);
    state_t state = A;

    always @(posedge clk) begin
        case (state)
            A: state <= B;
            B: state <= C;
            C: state <= D;
            default: state <= A;
        endcase
    end

    assign z = (state == B);
endmodule
*/