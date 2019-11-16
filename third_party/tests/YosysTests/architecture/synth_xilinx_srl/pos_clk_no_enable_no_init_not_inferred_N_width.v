// Check multi-bit works
// pos_clk_no_enable_no_init_not_inferred_N_width
(* top *)
module pos_clk_no_enable_no_init_not_inferred_N_width #(parameter width=130, depth=130) (input clk, input [width-1:0] i, output [width-1:0] q);
generate 
    wire [depth:0] int [width-1:0];
    genvar w, d;
    for (w = 0; w < width; w=w+1) begin
        assign int[w][0] = i[w];
        for (d = 0; d < depth; d=d+1) begin
            \$_DFFE_PP_ r(.C(clk), .D(int[w][d]), .E(1'b0), .Q(int[w][d+1]));
        end
        assign q[w] = int[w][depth];
    end
endgenerate
endmodule

`ifndef _AUTOTB
module __test ;
    wire [4095:0] assert_area = "cd pos_clk_no_enable_no_init_not_inferred_N_width; select t:FD* -assert-none";
endmodule
`endif
