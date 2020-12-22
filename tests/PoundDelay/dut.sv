module top;
property inq2(r1,r2);
@(posedge clk) a ##[r1:r2] b ##2 1'b1 |=> d;
endproperty
endmodule
