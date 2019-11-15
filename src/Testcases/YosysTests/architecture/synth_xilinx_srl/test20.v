(* top *)
module test20 #(parameter width=130, depth=130) (input clk, input [width-1:0] i, input e, output [width-1:0] q);
generate 
    reg [width-1:0] int [depth-1:0];

    genvar w, d;
    for (d = 0; d < depth; d=d+1) begin
        for (w = 0; w < width; w=w+1) begin
            initial int[d][w] <= ~((d+w) % 2);

            if (d == 0) begin
                always @(negedge clk) if (e) int[d][w] <= i[w];
            end
            else begin
                always @(negedge clk) if (e) int[d][w] <= int[d-1][w];
            end
        end
    end
    assign z = int[depth-1];
endgenerate
endmodule

`ifndef _AUTOTB
module __test ;
    wire [4095:0] assert_area = "cd test20; select t:FD* -assert-count 0";
endmodule
`endif
