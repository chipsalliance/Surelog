// Check that use of resets block shreg
// pos_clk_no_enable_no_init_not_inferred_with_reset_var_len
(* top *)
module pos_clk_no_enable_no_init_not_inferred_with_reset_var_len #(parameter width=1, depth=130) (input clk, input [width-1:0] i, input r, input [31:0] l, output [width-1:0] q);
generate 
    wire [depth:0] int [width-1:0];
    genvar w, d;
    for (w = 0; w < width; w=w+1) begin
        assign int[w][0] = i[w];
        for (d = 0; d < depth; d=d+1) begin
            \$_DFF_PP0_ r(.C(clk), .D(int[w][d]), .R(r), .Q(int[w][d+1]));
        end
        wire [depth-1:0] t;
        assign t = int[w][depth:1];
        assign q[w] = t[l];
    end
endgenerate
endmodule

`ifndef _AUTOTB
module __test ;
    wire [4095:0] assert_area = "cd pos_clk_no_enable_no_init_not_inferred_with_reset_var_len; select t:SRL* -assert-none";
endmodule
`endif
