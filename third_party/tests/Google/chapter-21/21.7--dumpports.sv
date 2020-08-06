/*
:name: vcd_dumpports_test
:description: vcd dump ports tests
:tags: 21.7
:type: simulation parsing
*/
module top();

integer i;
string fname = "out.vcd";

initial begin
	$dumpports(top, fname);
	$dumpportslimit(1024*1024, fname);

	i = 1;
	#100 i = 2;
	#200 $dumpportsoff(fname);
	i = 3;
	#800 $dumpportson(fname);
	i = 4;
	#100 $dumpportsflush(fname);
	i = 5;
	#300 $dumpportsall(fname);
	i = 6;
end

endmodule
