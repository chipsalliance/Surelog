module
 dff_nested(
input
 d, ck, pr, clr, 
output
 q, nq);
wire
 q1, nq1, nq2;
module
 ff1;
nand
 g1b (nq1, d, clr, q1);
nand
 g1a (q1, ck, nq2, nq1);
endmodule
    ff1 i1();

module
 ff2;
wire
 q2; // This wire can be encapsulated in ff2
nand
 g2b (nq2, ck, clr, q2);
nand
 g2a (q2, nq1, pr, nq2);
endmodule
    ff2 i2();
module
 ff3;
nand
 g3a (q, nq2, clr, nq);
nand
 g3b (nq, q1, pr, q);
endmodule
    ff3 i3();
endmodule
