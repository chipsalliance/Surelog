module testbench;
    reg en;

    initial begin
        // $dumpfile("testbench.vcd");
        // $dumpvars(0, testbench);

        #5 en = 0;
        repeat (10000) begin
            #5 en = 1;
            #5 en = 0;
        end

        $display("OKAY");
    end


    reg dinA = 0;
    wire doutB;
	reg lat = 0;

    top uut (
        .clk (en ),
        //.__1__ (dinA ),
        .__1b__ (doutB )
    );

    always @(posedge en) begin
    #3;
    dinA <= dinA + 1;
    end


    always @(* )
		if ( en )
            lat <= dinA;




	assert_dff lat_test(.clk(en), .test(doutB), .pat(lat));

endmodule
