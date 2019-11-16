
module cmp #(parameter real hyst = 0.65)

(input wire logic [0:1] inA,
input logic rst,
output
logic
 out);
initial
 out = 1'b0;
always
 @(inA, rst) 
begin
if
 (rst) out <= 1'b0;
else
if
 (inA[0] & ~inA[1]) out <= 1'b1;
else
out
 <= 1'b0;
end
endmodule
 : cmp
