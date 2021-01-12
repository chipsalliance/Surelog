
`include "inc.h"
//`define min(a,b) {(a) < (b) ? (a) : (b)}

module asym_ram ();
parameter WIDTHB = 4;
parameter WIDTHA = 4;

`define max(a,b) {(a) > (b) ? (a) : (b)}

//`define min(a,b) {(a) < (b) ? (a) : (b)}

function integer log2;
input integer value;
reg [31:0] shifted;
integer res;
begin
 if (value < 2)
  log2 = value;
 else
 begin
  shifted = value-1;
  for (res=0; shifted>0; res=res+1)
   shifted = shifted>>1;
  log2 = res;
 end
end
endfunction

localparam maxWIDTH = `max(WIDTHA, WIDTHB);



   
localparam minWIDTH = `min(WIDTHA, WIDTHB);


   
localparam RATIO = maxWIDTH / minWIDTH;

   
localparam log2RATIO = log2(RATIO);


endmodule // asym_ram
