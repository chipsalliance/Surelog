module testbench;
    reg clk;

    initial begin
       // $dumpfile("testbench.vcd");
       // $dumpvars(0, testbench);

        #0 clk = 0;
        repeat (10000) begin
            #5 clk = 1;
            #5 clk = 0;
        end

        $display("OKAY");
    end

    reg rst = 1;
    reg ce = 1;
    wire [3:0] count;
    reg [3:0] count_p;

	always @(posedge clk)
    begin
		rst = 0;
	end

	always @(posedge clk)
      if (rst)
         count_p <= 4'd0;
      else if (ce)
         count_p <= count_p + 4'd1;

	top uut (
        .clk(clk),
        .rst (rst ),
        .en (ce),
        .count (count)
    );

	genvar index;
	generate
	for (index=0; index <= 3; index=index+1)
	begin: gen_code_label
		assert_dff check_output(clk,count[index],count_p[index]);
	end
	endgenerate

endmodule
