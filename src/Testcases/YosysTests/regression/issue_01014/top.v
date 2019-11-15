module top (input [7:0] data, output [7:0] out);
genvar n;
generate
    for (n=7; n>=0; n=n-1) begin
        assign out[n] = data[7-n];
    end
endgenerate
endmodule
