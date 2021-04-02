module gen_test4();



genvar i;
generate
        for (i=0; i < 2; i=i+1) begin : foo
                if (i == 0)
                        assign temp1 = a;
                else
                        assign temp2 = b;
        end
endgenerate
endmodule
