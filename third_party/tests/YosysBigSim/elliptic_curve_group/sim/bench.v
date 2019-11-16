module testbench;

reg start_add = 0;
wire stop_add_start_mul;
wire stop_mul;

test_point_add test_add(start_add, stop_add_start_mul);
test_point_scalar_mult test_mul(stop_add_start_mul, stop_mul);

initial begin
	#100;
	start_add <= 1;
	@(posedge stop_mul);
	$finish;
end

endmodule
