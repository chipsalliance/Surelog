module
 cct (stim1, stim2);
input
stim1, stim2;
// instantiate mod
mod amod(stim1),
bmod(stim2);
endmodule
module
 mod (in);
input
 in;
always
@(
posedge
 in) 
begin
 : keep
logic
 hold;
hold = in;
end
endmodule
module
 wave;
logic
 stim1, stim2;
cct a(stim1, stim2); // instantiate cct
initial
begin
 :wave1
#100
fork
 :innerwave
reg hold;
join
#150 
begin
stim1 = 0;
end
end
endmodule