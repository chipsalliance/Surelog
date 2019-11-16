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



	reg i1,i2 = 0;
	wire o1g,o2g;
	wire o1r,o2r;
	wire o1w,o2w;
	wire o1gt,o2gt;
	wire o1rt,o2rt;
	wire o1wt,o2wt;

    always @(posedge clk) begin
		i1 <= i1 + 1;
		i2 <= i2 + 1;
    end


    gold uut_g (
		i1,i2,o1g,o2g
    );

    top_r uut_r (
		i1,i2,o1r,o2r
    );

    top_w uut_w (
		i1,i2,o1w,o2w
    );

    goldt uut_gt (
		i1,i2,o1gt,o2gt
    );

    top_rt uut_rt (
		i1,i2,o1rt,o2rt
    );

    top_wt uut_wt (
		i1,i2,o1wt,o2wt
    );


	assert_dff gold_test(clk,o1g,o1gt);
	assert_dff top_r_test(clk,o1r,o1rt);
	assert_dff top_w_test(clk,o1w,o1wt);
endmodule

module goldt(input i1, input i2, output o2, output o1);
 wire _1_;
 assign o2 = i1 & i2;
 assign _1_ = i1 | i2;
 assign o1 = _1_ & o2;
endmodule

module top_rt( i1, i2, o1, o2 );
  input i1, i2;
  output o1, o2;
  wire w4;
  assign o2 = (i2 & i1);
  assign w4 = ((i2 && i1) | (i2) | (i1));
  assign o1 = ((w4 & o2));
endmodule

module top_wt( i1, i2, o1, o2 );
  input i1, i2;
  output o1, o2;
  wire w4;
  assign o2 = (i2 & i1);
  assign w4 = ((i2 & i1) | (i2) | (i1));
  assign o1 = ((w4 & o2));
endmodule
