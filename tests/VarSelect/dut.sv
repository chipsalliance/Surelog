

module top();
	assign a[0][0] = 1'b0;

	logic [32:0] [32:0] test_net;
	initial begin
    for (int i=0; i<32; i++) begin
		test_net[i]    =   '0;
		test_net[i][i] = 1'b1;
	    end
	end;

endmodule

