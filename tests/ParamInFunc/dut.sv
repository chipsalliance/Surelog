`default_nettype none

module func_block_top(inp, out1, out2, out3);
        function automatic [31:0] func3;
                localparam A = 31;
                parameter B = 1 - 0;
                input [31:0] inp;
                func3[A:B] = inp[A:B];
        endfunction
endmodule
