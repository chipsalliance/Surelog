module mux2 (S,A,B,Y);
    input S;
    input A,B;
    output reg Y;
`ifndef BUG

    always @(*)
		Y = (S)? B : A;
`else

    always @(*)
		Y = (~S)? B : A;
`endif
endmodule

module mux4 ( S, D, Y );

input[1:0] S;
input[3:0] D;
output Y;

reg Y;
wire[1:0] S;
wire[3:0] D;

always @*
    if (S == 0) Y <= D[0];
    else if (S == 1) Y <= D[1];
    else if (S == 2) Y <= D[2];
    else if (S == 3) Y <= D[3];
    else Y <= 1'bx;

endmodule

module mux8 ( S, D, Y );

input[2:0] S;
input[7:0] D;
output Y;

reg Y;
wire[2:0] S;
wire[7:0] D;

always @*
    if (S == 0) Y <= D[0];
    else if (S == 1) Y <= D[1];
    else if (S == 2) Y <= D[2];
    else if (S == 3) Y <= D[3];
    else if (S == 4) Y <= D[4];
    else if (S == 5) Y <= D[5];
    else if (S == 6) Y <= D[6];
    else if (S == 7) Y <= D[7];
    else Y <= 1'bx;

endmodule

module mux16 (D, S, Y);
 	input  [15:0] D;
 	input  [3:0] S;
 	output Y;

reg Y;
wire[3:0] S;
wire[15:0] D;

always @*
     begin
        case( S )
            0 : Y = D[0];
            1 : Y = D[1];
            2 : Y = D[2];
            3 : Y = D[3];
     `ifndef BUG
            4 : Y = D[4];
     `else
            4 : Y = D[7];
     `endif
            5 : Y = D[5];
            6 : Y = D[6];
            7 : Y = D[7];
            8 : Y = D[8];
            9 : Y = D[9];
            10 : Y = D[10];
            11 : Y = D[11];
            12 : Y = D[12];
            13 : Y = D[13];
            14 : Y = D[14];
            15 : Y = D[15];
            default: Y = 1'bx;
        endcase
     end

endmodule


module top (
input [3:0] S,
input [15:0] D,
output M2,M4,M8,M16
);

mux2 u_mux2 (
        .S (S[0]),
        .A (D[0]),
        .B (D[1]),
        .Y (M2)
    );


mux4 u_mux4 (
        .S (S[1:0]),
        .D (D[3:0]),
        .Y (M4)
    );

mux8 u_mux8 (
        .S (S[2:0]),
        .D (D[7:0]),
        .Y (M8)
    );

mux16 u_mux16 (
        .S (S[3:0]),
        .D (D[15:0]),
        .Y (M16)
    );

endmodule
