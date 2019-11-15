module testbench;
    reg en;

    initial begin
         $dumpfile("testbench.vcd");
         $dumpvars(0, testbench);

        #5 en = 0;
        repeat (10000) begin
            #5 en = 1;
            #5 en = 0;
        end

        $display("OKAY");    
    end
   
    
    reg [2:0] dinA = 0;
    wire doutB,doutB1,doutB2,doutB3;
	reg lat,nlat,alat,alatn = 0;

    top uut (
        .en (en ),
        .a (dinA[0] ),
        .pre (dinA[1] ),
        .clr (dinA[2] ),
        .b (doutB ),
        .b1 (doutB1 ),
        .b2 (doutB2 ),
        .b3 (doutB3 )
    );
    
    always @(posedge en) begin
    #3;
    dinA <= dinA + 1;
    end
	
	always @( en or dinA[0] or dinA[1] or dinA[2] )
		if ( dinA[2] )
			lat <= 1'b0;
		else if ( dinA[1] )
			lat <= 1'b1;
		else if ( en )
            lat <= dinA[0];
    
    always @( en or dinA[0] or dinA[1] or dinA[2] )
		if ( !dinA[2] )
			nlat <= 1'b0;
		else if ( !dinA[1] )
			nlat <= 1'b1;
		else if (!en)
            nlat <= dinA[0];
            
    always @( en or dinA[0] or dinA[2] )
		if ( dinA[2] )
			alat <= 1'b0;
		else if (en)
            alat <= dinA[0];
            
    always @( en or dinA[0] or dinA[2] )
		if ( !dinA[2] )
			alatn <= 1'b0;
		else if (!en)
            alatn <= dinA[0];
            
            
	assert_dff lat_test(.clk(en), .test(doutB), .pat(lat));
    assert_dff nlat_test(.clk(en), .test(doutB1), .pat(nlat));
    assert_dff alat_test(.clk(en), .test(doutB2), .pat(alat));    
    assert_dff alatn_test(.clk(en), .test(doutB3), .pat(alatn));
    
endmodule
