module top (input [63:0] A, B, C, D, input [127:0] E, F, output reg [127:0] X, Y);
        integer i;
        always @* begin
                X = A*B + E;
                Y = F;
                for (i = 0; i < 64; i=i+1)
                        Y = Y + C[i]*D[i];
        end
endmodule
