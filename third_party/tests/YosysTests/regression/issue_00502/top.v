module top (A, B, C, Y);
    input    A, B, C;
    output   Y;

   MY_AND3 inst_t1 (.A(A), .B(B), .C(C), .Y(Y) );

endmodule

module MY_AND3 (A, B, C, Y);
    input    A, B, C;
    output   Y;

//   MY_AND2 inst_a1 (.A(A), .B(B), .Y(\\SUM/N10) ); // will not read
   MY_AND2 inst_a1 (.A(A), .B(B), .Y( \\SUM/N10 ) ); // needs whitespaces around net name
   MY_AND2 inst_a2 (.A(C), .B( \\SUM/N10 ), .Y(Y) );

endmodule

module MY_AND2 (A, B, Y);
    input     A, B;
    output    Y;

assign Y = A & B;

endmodule
