module template (input clk, input d, output reg q);
parameter neg_clk = 0;

initial q = 1'b1;

generate
    if (neg_clk) begin
        always @(negedge clk) q <= d;
    end
    else begin
        always @(posedge clk) q <= d;
    end
endgenerate
endmodule

module top(input clk, input d, output [1:0] q);
    template #(.neg_clk(1)) neg_clk(clk, d, q[0]);
    template #(.neg_clk(0)) pos_clk(clk, d, q[1]);
endmodule
