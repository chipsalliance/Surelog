module submod(output q);
wire aa = 1'b1;
assign q = aa;
endmodule

module top(output q);
wire \submod_i.aa ;
submod submod_i(.q(\submod_i.aa ));
assign q = \submod_i.aa ;
endmodule
