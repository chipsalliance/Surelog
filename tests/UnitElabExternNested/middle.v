
extern module m (a,b,c,d);
extern module a #(
parameter
 size= 8, 
parameter
type
 TP = 
logic
 [7:0]) 
 (
input
 [size:0] a, 
output
 TP b);


module top ();
wire
[8:0] a;
logic
 [7:0] b;
wire
c, d; 

m mm (.*);
a aa (.*);
endmodule


