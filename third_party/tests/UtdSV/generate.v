
module tb_generate;
genvar i;

generate
    for (i=0; i < 4; i=i+1) begin : MEM
      memory U (read, write, 
                data_in[(i*8)+7:(i*8)], 
                address,data_out[(i*8)+7:(i*8)]);
    end
endgenerate

endmodule
