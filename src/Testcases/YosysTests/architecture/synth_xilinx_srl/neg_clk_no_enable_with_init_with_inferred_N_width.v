// Check multi-bit works
// neg_clk_no_enable_with_init_with_inferred_N_width
(* top *)
module neg_clk_no_enable_with_init_with_inferred_N_width #(parameter width=130, depth=130) (input clk, input [width-1:0] i, output [width-1:0] q);
generate 
    reg [depth-1:0] int [width-1:0];

    genvar w, d;
    for (w = 0; w < width; w=w+1) begin
        for (d = 0; d < depth; d=d+1)
            initial int[w][d] <= ~((d+w) % 2);

        if (depth == 1) begin
            always @(negedge clk) int[w] <= i[w];
            assign q[w] = int[w];
        end
        else begin
            always @(negedge clk) int[w] <= { int[w][depth-2:0], i[w] };
            assign q[w] = int[w][depth-1];
        end
    end
endgenerate
endmodule

`ifndef _AUTOTB
module __test ;
    wire [4095:0] assert_area = "cd neg_clk_no_enable_with_init_with_inferred_N_width; select t:FD* -assert-none";
endmodule
`endif
