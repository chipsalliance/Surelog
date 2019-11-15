// Check that non chain users block SRLs
// (i.e. output port, in non flattened case)
// sr_var_length_other_users_port
(* top *)
module sr_var_length_other_users_port #(parameter width=1, depth=130) (input clk, input [width-1:0] i, input e, input [31:0] l, output [width-1:0] q, output [depth-1:0] state);
generate 
    reg [depth-1:0] int [width-1:0];

    genvar w, d;
    for (w = 0; w < width; w=w+1) begin
        for (d = 0; d < depth; d=d+1)
            initial int[w][d] <= ~((d+w) % 2);

        if (depth == 1) begin
            always @(negedge clk) if (e) int[w] <= i[w];
            assign q[w] = int[w];
        end
        else begin
            always @(negedge clk) if (e) int[w] <= {{ int[w][depth-2:0], i[w] }};
            assign q[w] = int[w][l];
        end
    end
    assign state = int[0];
endgenerate
endmodule

`ifndef _AUTOTB
module __test ;
    wire [4095:0] assert_area = "cd sr_var_length_other_users_port; select t:SRL* -assert-count 0";
endmodule
`endif
