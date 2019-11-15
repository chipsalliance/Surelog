

module test_top();

dbl_buf #(1,
2,3,
REG_WIDTH
+
64)
dbl_buf (.rst_l(rst_l),
                .clk(clk),
                .wr(dbl_buf_wr),
                .din(c2i_packet),
                .rd(dbl_buf_rd),
                .dout(outdata_buf_in),
                .vld(dbl_buf_vld),
                .full(dbl_buf_full));

module_being_instanced MODULE_NAME (
.serial_in       ({serial_in[87:72] } ),
.afo             ({afo[87:72] } ),
.serial_out      ({serial_out[87:72] } ),
.afi             ({afi[87:72] } ),
.vrefcode_i_l    ({net0527[0] ,net0527[1] ,net0527[2] ,net0527[3] ,
       net0527[4] ,net0527[5] ,net0527[6] ,net0527[7] } ),
.vrefcode_i_r    ({net0578[0] ,net0578[1] ,net0578[2] ,net0578[3] ,
       net0578[4] ,net0578[5] ,net0578[6] ,net0578[7] } ),
.data_neg        
     ({\dram_io_data_out[247] ,
       \dram_io_data_out[246] ,
       \dram_io_data_out[245] ,
       \dram_io_data_out[244] ,
       \dram_io_data_out[243] ,
       \dram_io_data_out[242] ,
       \dram_io_data_out[241] ,
       \dram_io_data_out[240] ,
       \dram_io_data_out[183] ,
       \dram_io_data_out[182] ,
       \dram_io_data_out[181] ,
       \dram_io_data_out[180] ,
       \dram_io_data_out[179] ,
       \dram_io_data_out[178] ,
       \dram_io_data_out[177] ,
       \dram_io_data_out[176] } )
);

endmodule
