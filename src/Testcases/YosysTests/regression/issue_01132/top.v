module mux_if_bal_3_1 #(parameter N=3, parameter W=1) (input [N*W-1:0] i, input [$clog2(N)-1:0] s, output reg [W-1:0] o);
always @* begin
    o <= {{W{{1'bx}}}};
    if (s[0] == 1'b0)
     if (s[1] == 1'b0)
      o <= i[0*W+:W];
     else
      o <= i[1*W+:W];
    else
     if (s[1] == 1'b0)
      o <= i[2*W+:W];
end
endmodule
