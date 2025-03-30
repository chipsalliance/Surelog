module top();

logic [15:0] a[1:0];
logic b[$bits(a)-1:0];

// Std 1800-2017, 20.7
// - $size shall return the number of elements in the dimension, which is equivalent to: $high - $low + 1.

logic c[$size(a)-1:0];
logic d[$high(a)-$low(a)+1:0];

generate
    for (genvar i=0; i<$size(a); i++) begin
        assign c[i] = 0;
    end
endgenerate

endmodule
