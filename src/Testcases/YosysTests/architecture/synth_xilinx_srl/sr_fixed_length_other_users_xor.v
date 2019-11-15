// Check that non chain users block SRLs
// (i.e. output port, in non flattened case)
// sr_fixed_length_other_users_xor
(* top *)
module sr_fixed_length_other_users_xor #(parameter width=1, depth=130) (input clk, input [width-1:0] i, input e, output [width-1:0] q, output [depth-1:0] state);
generate 
    wire [depth:0] int [width-1:0];
    genvar w, d;
    for (w = 0; w < width; w=w+1) begin
        assign int[w][0] = i[w];
        for (d = 0; d < depth; d=d+1) begin
            \$_DFFE_PP_ r(.C(clk), .D(int[w][d]), .E(1'b1), .Q(int[w][d+1]));
        end
        assign q[w] = int[w][depth];
    end
    assign state = int[0][depth:1];
endgenerate
endmodule

`ifndef _AUTOTB
module __test ;
    wire [4095:0] assert_area = "cd sr_fixed_length_other_users_xor; select t:SRL* -assert-count 0";
endmodule
`endif
