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


(* my_udp *)
primitive udp_sequential_initial(q, clk, d);
(* q = "blah" *)  output q; 
(* clk = "foo" *) input clk, d;

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

module udp_body_tb();

reg b,c;
wire a;

udp_body udp (a,b,c);

initial begin
  $monitor(" B = %b C = %b  A = %b",b,c,a);
  b = 0;
  c = 0;
  #1 b = 1;
  #1 b = 0;
  #1 c = 1;
  #1 b = 1'bx;
  #1 c = 0;
  #1 b = 1;
  #1 c = 1'bx;
  #1 b = 0;
  #1 $finish;
end  

endmodule

