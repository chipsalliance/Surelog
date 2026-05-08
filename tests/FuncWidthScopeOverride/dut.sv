module func_width_scope_top(inp, out1, out2);
    input wire signed inp;

    localparam WIDTH_A = 5;

    generate
        if (1) begin : blk
            localparam WIDTH_A = func_width_scope_top.WIDTH_A;
            function automatic [WIDTH_A-1:0] func2;
                input reg [WIDTH_A-1:0] inp;
                func2 = ~inp;
            endfunction
            wire [func2(0)-1:0] yc;
        end
    endgenerate

    output wire [1023:0] out1, out2;
    assign out1 = 0;
    assign out2 = 0;

endmodule
