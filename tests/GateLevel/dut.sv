module LogicGates(a,b,y1,y2,y3,y4,y5,y6,y7, y8, y9, y10);
  input a,b;
  output y1, y2,y3,y4,y5,y6,y7,y8,y9;
  
  and(y1,a,b);
  or(y2,a,b);
  not(y3,a);
  nand(y4,a,b);
  nor(y5,a,b);
  xor(y6,a,b);
  xnor(y7,a,b);

  and #(1)   a1 (y8,a,b);
  or #(1,2) a2 (y9,a,b, a | b);
  nand #(2:3:4, 3:4:5)  a3 (nn, a, b);
  bufif0 #(5, 6, 7) a4 (out2, a, b);
  bufif0 #(5:6:7, 6:7:8, 7:8:9) a5 (out3, a, b);
  pmos a6 (p1,p2,p3);
  pullup a7 (p1);
endmodule
