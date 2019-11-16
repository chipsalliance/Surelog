module top(
        alu_data_d_in,
    alu_data_d_out
    );

    input [7:0]alu_data_d_in;
    output[7:0]alu_data_d_out;
    wire [7:0]swap_out;
    genvar i;


    generate
        for ( i = 7 ; ( i >= 4 ) ; i = ( i - 1 ) )
        begin : swap_h
            assign swap_out[i] = alu_data_d_in[( ( i - 4 ) )];
        end
    endgenerate
     generate
         //for ( i = 0 ; ( i <4 ) ; i = ( i + 1 ) )  //OK
         for ( i = 3 ; ( i >=0 ) ; i = ( i - 1 ) ) //FAIL
         begin : swap_l
             assign swap_out[i] = alu_data_d_in[(i+4 )];
         end
     endgenerate

assign alu_data_d_out = swap_out;

endmodule
