// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


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
