module gen_test9;
        wire [1:0] w = 2'b11;
        generate
                begin : A
                        wire [1:0] x;
                        generate
                        begin : B
                                wire [1:0] y = 2'b00;
                        end
                        endgenerate
                        generate
                        begin : C
                                wire [1:0] z = 2'b01;
                        end
                        endgenerate
                        assign x = B.y ^ 2'b11 ^ C.z;
                end
        endgenerate
endmodule // gen_test9
