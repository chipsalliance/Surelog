module d_latch_gates(d,clk,q,q_bar);
input d,clk;
output q, q_bar;

wire n1,n2,n3;

not a (n1,d);
not a (n1,d), b(n2,c);
not c (n1,d),  (n2,c);
not                          (n1,d), b(n2,c);
not                        a (n1,d), b(n2,c);
not (supply0,supply1)      a (n1,d), b(n2,c);
not (supply0,supply1) #(1) a (n1,d), b(n2,c);
not a (n1,d), b(n2,c);
not #(1) a (n1,d), b(n2,c);
not #(1,2) a (n1,d), b(n2,c);

tranif0        (b,c,d);
tranif0      a (b,c,d);
tranif0 #(1)   (b,c,d);
tranif0 #(1) a (b,c,d);

bufif0        (b,c,d);
bufif0      a (b,c,d);
bufif0 #(1)   (b,c,d);
bufif0 #(1) a (b,c,d);


nand (n2,d,clk);
nand (n3,n1,clk);

nand (q,q_bar,n2);
nand (q_bar,q,n3);

endmodule
