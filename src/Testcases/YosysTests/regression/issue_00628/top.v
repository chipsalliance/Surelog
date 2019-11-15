module top (
	input a,
	output zro_zro, zro_not, zro_buf, zro_one,
	output not_zro, not_not, not_buf, not_one,
	output buf_zro, buf_not, buf_buf, buf_one,
	output one_zro, one_not, one_buf, one_one,
	output magic_inverter
);
	localparam [6:0] KEEP = 7'b1110001;
	localparam [6:0] FLIP = 7'b1101010;

	SB_LUT4 #(.LUT_INIT({1'b0, KEEP, KEEP, 1'b0})) magic_zro_zro (.I0(a), .I1(a), .I2(a), .I3(a), .O(zro_zro));
	SB_LUT4 #(.LUT_INIT({1'b0, KEEP, FLIP, 1'b0})) magic_zro_not (.I0(a), .I1(a), .I2(a), .I3(a), .O(zro_not));
	SB_LUT4 #(.LUT_INIT({1'b0, FLIP, KEEP, 1'b0})) magic_zro_buf (.I0(a), .I1(a), .I2(a), .I3(a), .O(zro_buf));
	SB_LUT4 #(.LUT_INIT({1'b0, FLIP, FLIP, 1'b0})) magic_zro_one (.I0(a), .I1(a), .I2(a), .I3(a), .O(zro_one));

	SB_LUT4 #(.LUT_INIT({1'b0, KEEP, FLIP, 1'b1})) magic_not_zro (.I0(a), .I1(a), .I2(a), .I3(a), .O(not_zro));
	SB_LUT4 #(.LUT_INIT({1'b0, KEEP, KEEP, 1'b1})) magic_not_not (.I0(a), .I1(a), .I2(a), .I3(a), .O(not_not));
	SB_LUT4 #(.LUT_INIT({1'b0, FLIP, FLIP, 1'b1})) magic_not_buf (.I0(a), .I1(a), .I2(a), .I3(a), .O(not_buf));
	SB_LUT4 #(.LUT_INIT({1'b0, FLIP, KEEP, 1'b1})) magic_not_one (.I0(a), .I1(a), .I2(a), .I3(a), .O(not_one));

	SB_LUT4 #(.LUT_INIT({1'b1, FLIP, KEEP, 1'b0})) magic_buf_zro (.I0(a), .I1(a), .I2(a), .I3(a), .O(buf_zro));
	SB_LUT4 #(.LUT_INIT({1'b1, FLIP, FLIP, 1'b0})) magic_buf_not (.I0(a), .I1(a), .I2(a), .I3(a), .O(buf_not));
	SB_LUT4 #(.LUT_INIT({1'b1, KEEP, KEEP, 1'b0})) magic_buf_buf (.I0(a), .I1(a), .I2(a), .I3(a), .O(buf_buf));
	SB_LUT4 #(.LUT_INIT({1'b1, KEEP, FLIP, 1'b0})) magic_buf_one (.I0(a), .I1(a), .I2(a), .I3(a), .O(buf_one));

	SB_LUT4 #(.LUT_INIT({1'b1, FLIP, FLIP, 1'b1})) magic_one_zro (.I0(a), .I1(a), .I2(a), .I3(a), .O(one_zro));
	SB_LUT4 #(.LUT_INIT({1'b1, FLIP, KEEP, 1'b1})) magic_one_not (.I0(a), .I1(a), .I2(a), .I3(a), .O(one_not));
	SB_LUT4 #(.LUT_INIT({1'b1, KEEP, FLIP, 1'b1})) magic_one_buf (.I0(a), .I1(a), .I2(a), .I3(a), .O(one_buf));
	SB_LUT4 #(.LUT_INIT({1'b1, KEEP, KEEP, 1'b1})) magic_one_one (.I0(a), .I1(a), .I2(a), .I3(a), .O(one_one));

	not (magic_inverter, a);
endmodule
