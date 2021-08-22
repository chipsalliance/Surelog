
module dut #()();
wire [220:0] hw2reg_wrap;
wire [237:0] notworking_indexed_part_select;
wire [10:0] working_bitselect;
assign {working_bitselect[5]} = hw2reg_wrap[203];
assign {notworking_indexed_part_select[50-:16]} = hw2reg_wrap[203-:16];
endmodule
