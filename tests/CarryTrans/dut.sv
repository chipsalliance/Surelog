module carry_rtl(input a, b, c,
		 output cout);
   assign cout = (a&b) | (a&c) | (b&c);

endmodule


module carry_gate(input a, b, c,
		  output cout);
   
wire x, y, z;
and g1(x, a, b);
and g2(y, a, c);
and g3(z, b, c);
or g4(cout, x, y, z);
endmodule

module carry_trans(input a, b, c, output cout);
   
wire i1, i2, i3, i4, cn;
  
wire zero = 1'b0;
wire one = 1'b1;  
  
tranif1 n1(i1,zero, a);
tranif1 n2(i1, zero, b);
tranif1 n3(cn, i1, c);
tranif1 n4(i2, zero, b);
tranif1 n5(cn, i2, a);
tranif0 p1(i3, one, a);
tranif0 p2(i3, one, b);
tranif0 p3(cn, i3, c);
tranif0 p4(i4, one, b);
tranif0 p5(cn, i4, a);
tranif1 n6(cout, zero, cn);
tranif0 p6(cout, one, cn);
endmodule 


