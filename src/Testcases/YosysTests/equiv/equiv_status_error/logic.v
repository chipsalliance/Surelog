
`timescale 1ns/10ps
`celldefine
module NOR2_X0X2 (A, B, Y);
input  A ;
input  B ;
output Y ;
wire I0_out;

   or  (I0_out, A, B);
   not (Y, I0_out);

endmodule
`endcelldefine


`timescale 1ns/10ps
`celldefine
module DFFARAS_X2X2(Q,QN,D,CLK,SN,RN);

input D,CLK,SN,RN;
output Q,QN;
reg Q,QN;


always @ (posedge CLK or negedge RN or negedge SN)

begin
if (!RN) begin
Q<=1'b0; 
QN<=1'b1;
end
else if (!SN) begin
Q<=1'b1;
QN<=1'b0;
end
else begin 
Q<=D;
QN<=!D;
end
end
endmodule
`endcelldefine


`timescale 1ns/10ps
`celldefine
module TIEHL (tiehi, tielo);
output  tiehi ;
output  tielo ;

assign tiehi = 1'b1;
assign tielo = 1'b0;
endmodule
`endcelldefine

`timescale 1ns/10ps
`celldefine

module INV_X2X2 (A, Y);
input  A ;
output Y ;

   not (Y, A);
/*
   specify
     // delay parameters
     specparam
       tplhl$A$Y = 0.23:0.23:0.23,
       tphlh$A$Y = 0.33:0.33:0.33;

     // path delays
     (A *> Y) = (tphlh$A$Y, tplhl$A$Y);

   endspecify
*/
endmodule
`endcelldefine
