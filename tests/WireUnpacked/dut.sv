module dut #() ();
wire [5:0] read_buf [0:100];
assign read_buf[0][1-:2] = 1'b1;
endmodule
