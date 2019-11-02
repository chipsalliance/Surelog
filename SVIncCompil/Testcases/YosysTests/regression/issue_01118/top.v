module top(output [3:0] o);
generate
    genvar i;
    for (i = 3; i >= 0; i = i-1) begin
        assign o[i] = 1'b0;
    end
endgenerate
endmodule
