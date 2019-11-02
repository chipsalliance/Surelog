// Check that use of resets block shreg
// neg_clk_no_enable_with_init_with_inferred_with_reset_var_len
(* top *)
module neg_clk_no_enable_with_init_with_inferred_with_reset_var_len #(parameter width=1, depth=130) (input clk, input [width-1:0] i, input r, input [31:0] l, output [width-1:0] q);
generate 
    reg [depth-1:0] int [width-1:0];

    genvar w, d;
    for (w = 0; w < width; w=w+1) begin
        for (d = 0; d < depth; d=d+1)
            initial int[w][d] <= ~((d+w) % 2);

        if (depth == 1) begin
            always @(negedge clk or posedge r) if (r) int[w] <= 1'b0; else int[w] <= a[w];
            assign q[w] = int[w];
        end
        else begin
            always @(negedge clk or posedge r) if (r) int[w] <= {width{1'b0}}; else int[w] <= {{ int[w][depth-2:0], i[w] }};
            assign q[w] = int[w][l];
        end
    end
endgenerate
endmodule

`ifndef _AUTOTB
module __test ;
    wire [4095:0] assert_area = "cd neg_clk_no_enable_with_init_with_inferred_with_reset_var_len; select t:SRL* -assert-none";
endmodule
`endif
