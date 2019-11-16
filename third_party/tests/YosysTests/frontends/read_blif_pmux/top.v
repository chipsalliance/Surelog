module top(C, S, Y);
input C;
input [1:0] S;
output reg [3:0] Y;

initial Y = 0;

always @(posedge C) begin
        case (S)
                2'b00: Y <= 4'b0001;
                2'b01: Y <= 4'b0010;
                2'b10: Y <= 4'b0100;
                2'b11: Y <= 4'b1000;
        endcase
end

endmodule
