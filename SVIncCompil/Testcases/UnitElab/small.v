module small_top();
   small_test #(1e1,2) u1();
endmodule

module small_test();

  
   parameter signed [3:0] SIZE = 1e1;
   parameter dummy = 5;
parameter p1 = 13'b100;

genvar
 i, j, k, m; 
generate
for
 (i=0; i<SIZE; i=i+1) 
begin
:B1
// scope B1[i] 
M1 N1();
// instantiates B1[i].N1
for
 (j=0; j<SIZE; j=j+1) 
begin
:B2      // scope B1[i].B2[j]
M2 N2();
// instantiates B1[i].B2[j].N2

for
 (k=0; k<SIZE; k=k+1) 
begin
:B3   // scope B1[i].B2[j].B3[k] 
M3 N3();                         // instantiates 
end
                                 //   B1[i].B2[j].B3[k].N3
end
if
 (i>0) 
begin
:B4
// scope B1[i].B4
for
 (m=0; m<SIZE; m=m+1) 
begin
:B5   // scope B1[i].B4.B5[m] 
M4 N4();
// instantiates 
end
                                 //   B1[i].B4.B5[m].N4
end
end
endgenerate

endmodule

