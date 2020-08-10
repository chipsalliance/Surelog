primitive udp_body (
  a, // Port a
  b, // Port b
  c  // Port c
  );
  output a;
  input b,c;
  
  // UDP function code here
  // A = B | C;
  table
   // B  C    : A
      ?  1    : 1;
      1  ?    : 1;
      0  0    : 0;
  endtable
  
endprimitive // udp_body


primitive udp_latch(q, clk, d) ;
output q;   
input clk, d;

reg q;

table
  //clk d    q     q+
  0     1  : ? :   1   ;
  0     0  : ? :   0   ;
  1     ?  : ? :   -   ; 
endtable

endprimitive


primitive udp_sequential(q, clk, d);
output q; 
input clk, d;

reg q;

table
// obtain output on rising edge of clk
// clk         d        q       q+
   (01)         0   :   ?   :   0   ;
   (01)         1   :   ?   :   1   ;
   (0?)         1   :   1   :   1   ;
   (0?)         0   :   0   :   0   ;
// ignore negative edge of clk
   (?0)         ?   :   ?   :   -   ; 
// ignore d changes on steady clk
   ?      (??)      :   ?   :   -   ;
 endtable

endprimitive // udp_sequential


primitive udp_sequential_initial(q, clk, d);
output q; 
input clk, d;

reg q;

initial 
  q = 0;

table
// obtain output on rising edge of clk
// clk         d        q       q+
   (01)         0   :   ?   :   0   ;
   (01)         1   :   ?   :   1   ;
   (0?)         1   :   1   :   1   ;
   (0?)         0   :   0   :   0   ;
// ignore negative edge of clk
   (?0)         ?   :   ?   :   -   ; 
// ignore d changes on steady clk
   ?      (??)      :   ?   :   -   ;
 endtable

endprimitive // udp_sequential_initial

